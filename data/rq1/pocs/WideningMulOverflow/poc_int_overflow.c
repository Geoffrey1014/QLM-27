/* PoC for "widening integer overflow flowing into a danger sink" (CWE-190 -> CWE-680).
 *
 * The pattern this query targets: an arithmetic op (a*b, a+b, 1<<n) is computed in a
 * small (<=4 byte) integer type, its result is then widened to a >4 byte type, AND
 * that result is used as a DANGER SINK:
 *   - allocation size  (kmalloc/kzalloc/kvmalloc/vmalloc/krealloc/devm_kmalloc/memdup_user, ...)
 *   - copy/set length  (memcpy/memmove/memset/copy_from_user/copy_to_user, ...)
 *   - a wider size/len/offset/count/width-like struct field store
 *
 * The C arithmetic is done in the SMALL type first, so it can overflow before being
 * widened. Fix = cast one operand to the wide type BEFORE the op ((u64)a * b).
 *
 * Naming convention:
 *   *_buggy : MUST be reported (widening overflow whose result reaches a danger sink).
 *   *_fixed : MUST NOT be reported, either (a) an operand is cast to the wide type before the op (the barrier),
 *             or (b) there is no widening, or the result never reaches a danger sink.
 */

typedef unsigned char      u8;
typedef unsigned short     u16;
typedef unsigned int       u32;
typedef unsigned long long u64;
typedef long long          loff_t;
typedef long long          sector_t;
typedef unsigned long      size_t;

/* ---- sink prototypes (size/length arg is the one that matters) ---- */
void *kmalloc(size_t size, unsigned flags);
void *kzalloc(size_t size, unsigned flags);
void *kvmalloc(size_t size, unsigned flags);
void *kmalloc_array(size_t n, size_t size, unsigned flags);
void *vmalloc(unsigned long size);
void *krealloc(void *p, size_t size, unsigned flags);
void *memcpy(void *d, const void *s, size_t n);
void *memmove(void *d, const void *s, size_t n);
void *memset(void *s, int c, size_t n);
unsigned long copy_from_user(void *to, const void *from, unsigned long n);

/* struct with WIDE size-like fields (the field-store sink). */
struct part {
    u64      size;      /* wider than u32 arith -> store is a sink */
    sector_t offset;
    u64      width;
};

/* ---------------- BUG cases (should be reported) ---------------- */

/* u32 * u32 -> u64, flows into kmalloc size. */
void *kmalloc_mul_buggy(u32 a, u32 b) {
    return kmalloc(a * b, 0);          /* BUG: a*b in 32-bit -> alloc size */
}

/* u32 * u32 via local var -> kzalloc size. */
void *kzalloc_mul_var_buggy(u32 n, u32 sz) {
    u64 total = n * sz;                /* BUG: 32-bit mul */
    return kzalloc(total, 0);          /* sink uses the widened local */
}

/* u32 + u32 -> kvmalloc size. */
void *kvmalloc_add_buggy(u32 a, u32 b) {
    u64 t = a + b;                     /* BUG: 32-bit add */
    return kvmalloc(t, 0);
}

/* int * int -> memcpy length. */
void memcpy_mul_buggy(void *d, void *s, int nblk, int blksz) {
    u64 len = nblk * blksz;           /* BUG: 32-bit mul -> copy len */
    memcpy(d, s, len);
}

/* u32 * u32 -> copy_from_user length. */
void copyfromuser_mul_buggy(void *to, void *from, u32 cnt, u32 esz) {
    copy_from_user(to, from, cnt * esz);  /* BUG: directly in len arg */
}

/* u16 * u16 (promoted to int, mul in 32-bit) -> memset length. */
void memset_mul_buggy(void *p, u16 w, u16 h) {
    memset(p, 0, w * h);              /* BUG: promoted to int -> set len */
}

/* widened-store-to-field sink (mirrors GT 9b458e8b / 5a4510c7). */
void field_store_mul_buggy(struct part *parts, u32 erasesize, u32 firstUnit) {
    parts->size = erasesize * firstUnit;   /* BUG: u32*u32 stored to u64 field */
}

void field_store_sector_buggy(struct part *p, u32 stripe, u32 chunk) {
    p->offset = stripe * chunk;            /* BUG: u32*u32 stored to sector_t field */
}

/* ---------------- OK cases: operand cast before op (should NOT be reported) ---------------- */

void *kmalloc_cast_fixed(u32 a, u32 b) {
    return kmalloc((u64)a * b, 0);     /* OK: left operand widened first */
}

void *kzalloc_cast_right_fixed(u32 a, u32 b) {
    u64 total = a * (u64)b;            /* OK */
    return kzalloc(total, 0);
}

void memcpy_cast_fixed(void *d, void *s, int nblk, int blksz) {
    u64 len = (u64)nblk * blksz;      /* OK: widened before mul */
    memcpy(d, s, len);
}

void field_store_cast_fixed(struct part *parts, u32 erasesize, u32 firstUnit) {
    parts->size = (u64)erasesize * firstUnit;  /* OK */
}

/* ---------------- SAFE cases: no danger sink, or no widening ---------------- */

/* widening op but result NOT used in a sink (just returned). */
u64 mul_no_sink_fixed(u32 a, u32 b) {
    u64 size = a * b;                 /* SAFE: never reaches a sink */
    return size;
}

/* widening op but used in a non-sink call. */
void noop(u64 v);
void mul_nonsink_call_fixed(u32 a, u32 b) {
    noop(a * b);                      /* SAFE: noop is not a danger sink */
}

/* sink size is a same-width (u64*u64) computation -> no overflow. */
void *kmalloc_wide_fixed(u64 a, u64 b) {
    return kmalloc(a * b, 0);         /* SAFE: 64-bit mul, no widening */
}

/* sink size is a 32-bit result used as 32-bit (no widening context here, but
 * kmalloc's size_t is 64-bit so this WOULD widen at the call). Use constant to be safe. */
void *kmalloc_const_fixed(void) {
    return kmalloc(4096, 0);          /* SAFE: constant size */
}

/* field store but field is same width as arith (u32 field). */
struct narrow { u32 size; };
void field_store_narrow_fixed(struct narrow *n, u32 a, u32 b) {
    n->size = a * b;                  /* SAFE: u32 field, no widening */
}

/* memcpy length is a wide-typed computation already. */
void memcpy_wide_fixed(void *d, void *s, u64 a, u64 b) {
    memcpy(d, s, a * b);             /* SAFE: 64-bit mul */
}
