/* QLM seed slice: drivers/pci/endpoint/functions/pci-epf-test.c @ 9f96b9b7d836 (fixed).
 * Function text below the preamble is verbatim from the kernel tree. */
#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

#define __iomem

typedef unsigned long phys_addr_t;
typedef unsigned int u32;
typedef unsigned int gfp_t;

#define GFP_KERNEL ((gfp_t)0)
#define ENOMEM 12
#define STATUS_DST_ADDR_INVALID (1 << 7)

enum pci_barno {
    BAR_0, BAR_1, BAR_2, BAR_3, BAR_4, BAR_5,
};

struct device {
    int dummy;
};

struct pci_epc;

struct pci_epf {
    struct device dev;
    struct pci_epc *epc;
    unsigned char func_no;
};

struct pci_epf_test_reg {
    u32 size;
    u32 status;
    u32 checksum;
    unsigned long long dst_addr;
};

struct pci_epf_test {
    struct pci_epf *epf;
    enum pci_barno test_reg_bar;
    struct pci_epf_test_reg *reg[6];
};

extern void *pci_epc_mem_alloc_addr(struct pci_epc *epc, phys_addr_t *phys_addr, size_t size);
extern void pci_epc_mem_free_addr(struct pci_epc *epc, phys_addr_t phys_addr, void *virt_addr, size_t size);
extern int pci_epc_map_addr(struct pci_epc *epc, unsigned char func_no, phys_addr_t phys_addr, unsigned long long pci_addr, size_t size);
extern void pci_epc_unmap_addr(struct pci_epc *epc, unsigned char func_no, phys_addr_t phys_addr);

extern void *kzalloc(size_t size, gfp_t flags);
extern void kfree(const void *ptr);
extern void get_random_bytes(void *buf, int nbytes);
extern u32 crc32_le(u32 crc, const void *buf, size_t len);
extern void *memcpy(void *dest, const void *src, size_t n);
extern void mdelay(unsigned long msecs);
extern void usleep_range(unsigned long min, unsigned long max);

extern void dev_err(const struct device *dev, const char *fmt, ...);

/* ---- verbatim kernel code ---- */
static int pci_epf_test_write(struct pci_epf_test *epf_test)
{
	int ret;
	void __iomem *dst_addr;
	void *buf;
	phys_addr_t phys_addr;
	struct pci_epf *epf = epf_test->epf;
	struct device *dev = &epf->dev;
	struct pci_epc *epc = epf->epc;
	enum pci_barno test_reg_bar = epf_test->test_reg_bar;
	struct pci_epf_test_reg *reg = epf_test->reg[test_reg_bar];

	dst_addr = pci_epc_mem_alloc_addr(epc, &phys_addr, reg->size);
	if (!dst_addr) {
		dev_err(dev, "failed to allocate address\n");
		reg->status = STATUS_DST_ADDR_INVALID;
		ret = -ENOMEM;
		goto err;
	}

	ret = pci_epc_map_addr(epc, epf->func_no, phys_addr, reg->dst_addr,
			       reg->size);
	if (ret) {
		dev_err(dev, "failed to map address\n");
		reg->status = STATUS_DST_ADDR_INVALID;
		goto err_addr;
	}

	buf = kzalloc(reg->size, GFP_KERNEL);
	if (!buf) {
		ret = -ENOMEM;
		goto err_map_addr;
	}

	get_random_bytes(buf, reg->size);
	reg->checksum = crc32_le(~0, buf, reg->size);

	memcpy(dst_addr, buf, reg->size);

	/*
	 * wait 1ms inorder for the write to complete. Without this delay L3
	 * error in observed in the host system.
	 */
	usleep_range(1000, 2000);

	kfree(buf);

err_map_addr:
	pci_epc_unmap_addr(epc, epf->func_no, phys_addr);

err_addr:
	pci_epc_mem_free_addr(epc, phys_addr, dst_addr, reg->size);

err:
	return ret;
}
