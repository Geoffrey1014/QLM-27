/* QLM seed slice: kernel/kexec_file.c @ 31d82c2c787d (fixed).
 * Function text below the preamble is verbatim from the kernel tree. */
#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

typedef unsigned long size_t_dummy;

#define GFP_KERNEL 0
#define ENOMEM 12
#define PAGE_SHIFT 12
#define PAGE_SIZE (1UL << PAGE_SHIFT)
#define SHA256_DIGEST_SIZE 32
#define KEXEC_SEGMENT_MAX 16

#define IS_ENABLED(x) (0)
#define CONFIG_ARCH_HAS_KEXEC_PURGATORY 0

#define IS_ERR(ptr) ((unsigned long)(void *)(ptr) >= (unsigned long)-4095)
#define PTR_ERR(ptr) ((long)(ptr))

#define ZERO_PAGE(x) ((void *)0)
#define __va(x) ((void *)(unsigned long)(x))

struct crypto_shash;

struct shash_desc {
    struct crypto_shash *tfm;
};

struct purgatory_info {
    void *purgatory_buf;
};

struct kexec_segment {
    void *kbuf;
    unsigned long mem;
    unsigned long bufsz;
    size_t memsz;
};

struct kimage {
    unsigned int nr_segments;
    struct kexec_segment segment[KEXEC_SEGMENT_MAX];
    struct purgatory_info purgatory_info;
};

struct kexec_sha_region {
    unsigned long start;
    unsigned long len;
};

extern struct crypto_shash *crypto_alloc_shash(const char *alg_name, unsigned int type, unsigned int mask);
extern unsigned int crypto_shash_descsize(struct crypto_shash *tfm);
extern int crypto_shash_init(struct shash_desc *desc);
extern int crypto_shash_update(struct shash_desc *desc, const void *data, unsigned int len);
extern int crypto_shash_final(struct shash_desc *desc, unsigned char *out);

extern void *kzalloc(size_t size, unsigned int flags);
extern void kfree(const void *objp);
extern void *vzalloc(unsigned long size);
extern void vfree(const void *addr);

extern unsigned long page_to_pfn(void *page);

extern int kexec_purgatory_get_set_symbol(struct kimage *image, const char *name,
                                          void *buf, unsigned int size, int get_value);

/* ---- verbatim kernel code ---- */
static int kexec_calculate_store_digests(struct kimage *image)
{
	struct crypto_shash *tfm;
	struct shash_desc *desc;
	int ret = 0, i, j, zero_buf_sz, sha_region_sz;
	size_t desc_size, nullsz;
	char *digest;
	void *zero_buf;
	struct kexec_sha_region *sha_regions;
	struct purgatory_info *pi = &image->purgatory_info;

	if (!IS_ENABLED(CONFIG_ARCH_HAS_KEXEC_PURGATORY))
		return 0;

	zero_buf = __va(page_to_pfn(ZERO_PAGE(0)) << PAGE_SHIFT);
	zero_buf_sz = PAGE_SIZE;

	tfm = crypto_alloc_shash("sha256", 0, 0);
	if (IS_ERR(tfm)) {
		ret = PTR_ERR(tfm);
		goto out;
	}

	desc_size = crypto_shash_descsize(tfm) + sizeof(*desc);
	desc = kzalloc(desc_size, GFP_KERNEL);
	if (!desc) {
		ret = -ENOMEM;
		goto out_free_tfm;
	}

	sha_region_sz = KEXEC_SEGMENT_MAX * sizeof(struct kexec_sha_region);
	sha_regions = vzalloc(sha_region_sz);
	if (!sha_regions) {
		ret = -ENOMEM;
		goto out_free_desc;
	}

	desc->tfm   = tfm;

	ret = crypto_shash_init(desc);
	if (ret < 0)
		goto out_free_sha_regions;

	digest = kzalloc(SHA256_DIGEST_SIZE, GFP_KERNEL);
	if (!digest) {
		ret = -ENOMEM;
		goto out_free_sha_regions;
	}

	for (j = i = 0; i < image->nr_segments; i++) {
		struct kexec_segment *ksegment;

		ksegment = &image->segment[i];
		/*
		 * Skip purgatory as it will be modified once we put digest
		 * info in purgatory.
		 */
		if (ksegment->kbuf == pi->purgatory_buf)
			continue;

		ret = crypto_shash_update(desc, ksegment->kbuf,
					  ksegment->bufsz);
		if (ret)
			break;

		/*
		 * Assume rest of the buffer is filled with zero and
		 * update digest accordingly.
		 */
		nullsz = ksegment->memsz - ksegment->bufsz;
		while (nullsz) {
			unsigned long bytes = nullsz;

			if (bytes > zero_buf_sz)
				bytes = zero_buf_sz;
			ret = crypto_shash_update(desc, zero_buf, bytes);
			if (ret)
				break;
			nullsz -= bytes;
		}

		if (ret)
			break;

		sha_regions[j].start = ksegment->mem;
		sha_regions[j].len = ksegment->memsz;
		j++;
	}

	if (!ret) {
		ret = crypto_shash_final(desc, digest);
		if (ret)
			goto out_free_digest;
		ret = kexec_purgatory_get_set_symbol(image, "purgatory_sha_regions",
						     sha_regions, sha_region_sz, 0);
		if (ret)
			goto out_free_digest;

		ret = kexec_purgatory_get_set_symbol(image, "purgatory_sha256_digest",
						     digest, SHA256_DIGEST_SIZE, 0);
		if (ret)
			goto out_free_digest;
	}

out_free_digest:
	kfree(digest);
out_free_sha_regions:
	vfree(sha_regions);
out_free_desc:
	kfree(desc);
out_free_tfm:
	kfree(tfm);
out:
	return ret;
}
