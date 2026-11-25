/*
 * PoC for the "unvalidated array index from external data" (CWE-129) pattern.
 * Mirrors the shapes of the ground-truth fixes:
 *   a402532 (usb bdc), 129fa60 (btusb), 0fd56fa (wl1251), 95dffe3 (aiptek),
 *   304950a (brcmfmac).
 *
 * Each *_buggy function should be flagged by UnvalidatedArrayIndex.ql.
 * Each *_fixed function should NOT be flagged.
 */
#include <stddef.h>
#include <stdint.h>

/* ---- fakes for kernel helpers / endian ---- */
static inline uint16_t get_unaligned_le16(const void *p) {
    const uint8_t *b = p;
    return (uint16_t)(b[0] | (b[1] << 8));
}
static inline uint32_t le32_to_cpu(uint32_t x) { return x; }
static inline uint16_t le16_to_cpu(uint16_t x) { return x; }
#define ARRAY_SIZE(a) (sizeof(a) / sizeof((a)[0]))

/* ---- external/firmware data structs ---- */
struct sreport { uint32_t offset[4]; };          /* hardware status report */
struct tx_result { uint8_t id; };                /* firmware completion */
struct if_event { uint8_t bsscfgidx; };          /* parsed network event */

static int g_table[8];
static int macroKeyEvents[25];
static const int alts[3] = { 2, 4, 5 };
static void *iflist[16];

/* ===== BUGGY: external field index, no bounds check ===== */

/* like bdc: (sreport->offset[3]>>4)&0x1f indexes a fixed table, no check */
int field_masked_buggy(struct sreport *sr) {
    unsigned int idx = (le32_to_cpu(sr->offset[3]) >> 4) & 0x1f;  /* 0..31 */
    return g_table[idx];                                          /* size 8: OOB */
}

/* like wl1251: direct field index, no check */
void *direct_field_buggy(struct tx_result *r) {
    return iflist[r->id];                                         /* no check */
}

/* like brcmfmac: field index into fixed iflist */
void *event_field_buggy(struct if_event *ev) {
    return iflist[ev->bsscfgidx];
}

/* like aiptek: local var from get_unaligned_le16, index = macro - 1, no check */
int unaligned_minus1_buggy(const uint8_t *data) {
    int macro = get_unaligned_le16(data + 1);
    return macroKeyEvents[macro - 1];                            /* no check */
}

/* like btusb: local var from field, index = sco_num - 1, no check */
int field_minus1_buggy(struct tx_result *r) {
    unsigned int sco = r->id;
    return alts[sco - 1];                                        /* size 3: OOB */
}

/* ===== FIXED: same shapes WITH bounds check (must NOT flag) ===== */

int field_masked_fixed(struct sreport *sr) {
    unsigned int idx = (le32_to_cpu(sr->offset[3]) >> 4) & 0x1f;
    if (idx >= ARRAY_SIZE(g_table))
        return -1;
    return g_table[idx];
}

void *direct_field_fixed(struct tx_result *r) {
    if (r->id >= ARRAY_SIZE(iflist))
        return NULL;
    return iflist[r->id];
}

int unaligned_minus1_fixed(const uint8_t *data) {
    int macro = get_unaligned_le16(data + 1);
    if (macro <= 0 || macro - 1 >= (int)ARRAY_SIZE(macroKeyEvents))
        return -1;
    return macroKeyEvents[macro - 1];
}

/* ===== SAFE: index not external / provably bounded (must NOT flag) ===== */

/* loop index, not external */
int loop_index_fixed(void) {
    int sum = 0;
    for (int i = 0; i < (int)ARRAY_SIZE(g_table); i++)
        sum += g_table[i];
    return sum;
}

/* constant index */
int const_index_fixed(void) {
    return g_table[3];
}
