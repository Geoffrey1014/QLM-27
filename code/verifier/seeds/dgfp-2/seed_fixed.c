/* QLM seed slice: drivers/crypto/cavium/cpt/cptpf_main.c @ e9acf05255cb (fixed).
 * Function text below the preamble is verbatim from the kernel tree. */
#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

typedef unsigned long long u64;
typedef unsigned int u32;
typedef unsigned short u16;
typedef unsigned char u8;

#define ENODEV 19
#define CPT_FLAG_DEVICE_READY 0x1

struct device {
    int _unused;
};

struct pci_dev {
    struct device dev;
};

struct cpt_device {
    struct pci_dev *pdev;
    int next_mc_idx;
    int next_group;
    unsigned int flags;
};

extern void mdelay(unsigned long msecs);
extern void msleep(unsigned int msecs);
extern int cpt_check_bist_status(struct cpt_device *cpt);
extern u64 cpt_check_exe_bist_status(struct cpt_device *cpt);
extern void cpt_reset(struct cpt_device *cpt);
extern void cpt_find_max_enabled_cores(struct cpt_device *cpt);
extern void cpt_disable_all_cores(struct cpt_device *cpt);
extern int dev_err(const struct device *dev, const char *fmt, ...);

/* ---- verbatim kernel code ---- */
static int cpt_device_init(struct cpt_device *cpt)
{
	u64 bist;
	struct device *dev = &cpt->pdev->dev;

	/* Reset the PF when probed first */
	cpt_reset(cpt);
	msleep(100);

	/*Check BIST status*/
	bist = (u64)cpt_check_bist_status(cpt);
	if (bist) {
		dev_err(dev, "RAM BIST failed with code 0x%llx", bist);
		return -ENODEV;
	}

	bist = cpt_check_exe_bist_status(cpt);
	if (bist) {
		dev_err(dev, "Engine BIST failed with code 0x%llx", bist);
		return -ENODEV;
	}

	/*Get CLK frequency*/
	/*Get max enabled cores */
	cpt_find_max_enabled_cores(cpt);
	/*Disable all cores*/
	cpt_disable_all_cores(cpt);
	/*Reset device parameters*/
	cpt->next_mc_idx   = 0;
	cpt->next_group = 0;
	/* PF is ready */
	cpt->flags |= CPT_FLAG_DEVICE_READY;

	return 0;
}
