/* QLM seed slice: drivers/ata/pata_octeon_cf.c @ 10d6bdf53290 (fixed).
 * Function text below the preamble is verbatim from the kernel tree. */
#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

#define __iomem
#define __init

typedef unsigned char u8;
typedef unsigned short u16;
typedef unsigned int u32;
typedef unsigned long long u64;
typedef unsigned int __be32;

#define GFP_KERNEL 0
#define EINVAL 22
#define ENOMEM 12
#define IORESOURCE_MEM 0x00000200
#define ATA_PIO6 0x40
#define ATA_FLAG_NO_ATAPI (1 << 6)
#define ATA_FLAG_PIO_POLLING (1 << 7)
#define ATA_MWDMA4 0x10
#define CLOCK_MONOTONIC 1
#define HRTIMER_MODE_REL 1
#define IRQF_SHARED 0x00000080
#define DRV_VERSION "0.0"
#define DMA_BIT_MASK(n) (((n) == 64) ? ~0ULL : ((1ULL << (n)) - 1))

#define ATA_REG_DATA    0
#define ATA_REG_ERR     1
#define ATA_REG_FEATURE 1
#define ATA_REG_NSECT   2
#define ATA_REG_LBAL    3
#define ATA_REG_LBAM    4
#define ATA_REG_LBAH    5
#define ATA_REG_DEVICE  6
#define ATA_REG_STATUS  7
#define ATA_REG_CMD     7

enum hrtimer_restart { HRTIMER_NORESTART = 0, HRTIMER_RESTART = 1 };

typedef int clockid_t;

struct hrtimer {
    enum hrtimer_restart (*function)(struct hrtimer *);
};

struct device_node;

struct device {
    struct device_node *of_node;
    void *platform_data;
};

struct resource {
    unsigned long start;
    unsigned long end;
    unsigned long flags;
};

struct property {
    const char *name;
    int length;
    void *value;
    struct property *next;
};

struct platform_device {
    struct device dev;
};

struct ata_ioports {
    void __iomem *cmd_addr;
    void __iomem *data_addr;
    void __iomem *error_addr;
    void __iomem *feature_addr;
    void __iomem *nsect_addr;
    void __iomem *lbal_addr;
    void __iomem *lbam_addr;
    void __iomem *lbah_addr;
    void __iomem *device_addr;
    void __iomem *status_addr;
    void __iomem *command_addr;
    void __iomem *altstatus_addr;
    void __iomem *ctl_addr;
    void __iomem *bmdma_addr;
    void __iomem *scr_addr;
};

struct ata_port_operations {
    void (*sff_data_xfer)(void);
    void (*softreset)(void);
    void (*sff_check_status)(void);
    void (*sff_tf_read)(void);
    void (*sff_tf_load)(void);
    void (*sff_exec_command)(void);
};

struct ata_port {
    void *private_data;
    struct ata_port_operations *ops;
    unsigned long pio_mask;
    unsigned long mwdma_mask;
    unsigned long flags;
    struct ata_ioports ioaddr;
};

struct ata_host {
    struct ata_port *ports[1];
};

struct octeon_cf_port {
    bool is_true_ide;
    u32 cs0;
    u32 cs1;
    u64 dma_base;
    struct ata_port *ap;
    struct hrtimer delayed_finish;
    void __iomem *c0;
};

typedef int (*irq_handler_t)(int, void *);

struct scsi_host_template;

extern void *devm_kzalloc(struct device *dev, size_t size, unsigned flags);
extern bool of_property_read_bool(const struct device_node *np, const char *propname);
extern int of_property_read_u32(const struct device_node *np, const char *propname, u32 *out);
extern int of_n_addr_cells(struct device_node *np);
extern int of_n_size_cells(struct device_node *np);
extern struct property *of_find_property(const struct device_node *np, const char *name, int *lenp);
extern u32 be32_to_cpup(const __be32 *p);
extern struct device_node *of_parse_phandle(const struct device_node *np, const char *phandle_name, int index);
extern struct platform_device *of_find_device_by_node(struct device_node *np);
extern struct resource *platform_get_resource(struct platform_device *pdev, unsigned int type, unsigned int num);
extern void of_node_put(struct device_node *node);
extern void put_device(struct device *dev);
extern void __iomem *devm_ioremap(struct device *dev, unsigned long offset, unsigned long size);
extern unsigned long resource_size(const struct resource *res);
extern int platform_get_irq(struct platform_device *pdev, unsigned int num);
extern struct ata_host *ata_host_alloc(struct device *dev, int n_ports);
extern void ata_sff_std_ports(struct ata_ioports *ioaddr);
extern void hrtimer_init(struct hrtimer *timer, clockid_t which_clock, int mode);
extern int dma_coerce_mask_and_coherent(struct device *dev, u64 mask);
extern void ata_port_desc(struct ata_port *ap, const char *fmt, ...);
extern void dev_info(struct device *dev, const char *fmt, ...);
extern int ata_host_activate(struct ata_host *host, int irq, irq_handler_t irq_handler,
                             unsigned long irq_flags, struct scsi_host_template *sht);

extern struct ata_port_operations octeon_cf_ops;
extern struct scsi_host_template octeon_cf_sht;
extern int enable_dma;

extern int octeon_cf_interrupt(int irq, void *dev_id);
extern void octeon_cf_data_xfer8(void);
extern void octeon_cf_data_xfer16(void);
extern enum hrtimer_restart octeon_cf_delayed_finish(struct hrtimer *t);
extern void octeon_cf_softreset16(void);
extern void octeon_cf_check_status16(void);
extern void octeon_cf_tf_read16(void);
extern void octeon_cf_tf_load16(void);
extern void octeon_cf_exec_command16(void);

/* ---- verbatim kernel code ---- */
static int octeon_cf_probe(struct platform_device *pdev)
{
	struct resource *res_cs0, *res_cs1;

	bool is_16bit;
	const __be32 *cs_num;
	struct property *reg_prop;
	int n_addr, n_size, reg_len;
	struct device_node *node;
	void __iomem *cs0;
	void __iomem *cs1 = NULL;
	struct ata_host *host;
	struct ata_port *ap;
	int irq = 0;
	irq_handler_t irq_handler = NULL;
	void __iomem *base;
	struct octeon_cf_port *cf_port;
	int rv = -ENOMEM;
	u32 bus_width;

	node = pdev->dev.of_node;
	if (node == NULL)
		return -EINVAL;

	cf_port = devm_kzalloc(&pdev->dev, sizeof(*cf_port), GFP_KERNEL);
	if (!cf_port)
		return -ENOMEM;

	cf_port->is_true_ide = of_property_read_bool(node, "cavium,true-ide");

	if (of_property_read_u32(node, "cavium,bus-width", &bus_width) == 0)
		is_16bit = (bus_width == 16);
	else
		is_16bit = false;

	n_addr = of_n_addr_cells(node);
	n_size = of_n_size_cells(node);

	reg_prop = of_find_property(node, "reg", &reg_len);
	if (!reg_prop || reg_len < sizeof(__be32))
		return -EINVAL;

	cs_num = reg_prop->value;
	cf_port->cs0 = be32_to_cpup(cs_num);

	if (cf_port->is_true_ide) {
		struct device_node *dma_node;
		dma_node = of_parse_phandle(node,
					    "cavium,dma-engine-handle", 0);
		if (dma_node) {
			struct platform_device *dma_dev;
			dma_dev = of_find_device_by_node(dma_node);
			if (dma_dev) {
				struct resource *res_dma;
				int i;
				res_dma = platform_get_resource(dma_dev, IORESOURCE_MEM, 0);
				if (!res_dma) {
					put_device(&dma_dev->dev);
					of_node_put(dma_node);
					return -EINVAL;
				}
				cf_port->dma_base = (u64)devm_ioremap(&pdev->dev, res_dma->start,
									 resource_size(res_dma));
				if (!cf_port->dma_base) {
					put_device(&dma_dev->dev);
					of_node_put(dma_node);
					return -EINVAL;
				}

				i = platform_get_irq(dma_dev, 0);
				if (i > 0) {
					irq = i;
					irq_handler = octeon_cf_interrupt;
				}
				put_device(&dma_dev->dev);
			}
			of_node_put(dma_node);
		}
		res_cs1 = platform_get_resource(pdev, IORESOURCE_MEM, 1);
		if (!res_cs1)
			return -EINVAL;

		cs1 = devm_ioremap(&pdev->dev, res_cs1->start,
					   resource_size(res_cs1));
		if (!cs1)
			return rv;

		if (reg_len < (n_addr + n_size + 1) * sizeof(__be32))
			return -EINVAL;

		cs_num += n_addr + n_size;
		cf_port->cs1 = be32_to_cpup(cs_num);
	}

	res_cs0 = platform_get_resource(pdev, IORESOURCE_MEM, 0);
	if (!res_cs0)
		return -EINVAL;

	cs0 = devm_ioremap(&pdev->dev, res_cs0->start,
				   resource_size(res_cs0));
	if (!cs0)
		return rv;

	/* allocate host */
	host = ata_host_alloc(&pdev->dev, 1);
	if (!host)
		return rv;

	ap = host->ports[0];
	ap->private_data = cf_port;
	pdev->dev.platform_data = cf_port;
	cf_port->ap = ap;
	ap->ops = &octeon_cf_ops;
	ap->pio_mask = ATA_PIO6;
	ap->flags |= ATA_FLAG_NO_ATAPI | ATA_FLAG_PIO_POLLING;

	if (!is_16bit) {
		base = cs0 + 0x800;
		ap->ioaddr.cmd_addr	= base;
		ata_sff_std_ports(&ap->ioaddr);

		ap->ioaddr.altstatus_addr = base + 0xe;
		ap->ioaddr.ctl_addr	= base + 0xe;
		octeon_cf_ops.sff_data_xfer = octeon_cf_data_xfer8;
	} else if (cf_port->is_true_ide) {
		base = cs0;
		ap->ioaddr.cmd_addr	= base + (ATA_REG_CMD << 1) + 1;
		ap->ioaddr.data_addr	= base + (ATA_REG_DATA << 1);
		ap->ioaddr.error_addr	= base + (ATA_REG_ERR << 1) + 1;
		ap->ioaddr.feature_addr	= base + (ATA_REG_FEATURE << 1) + 1;
		ap->ioaddr.nsect_addr	= base + (ATA_REG_NSECT << 1) + 1;
		ap->ioaddr.lbal_addr	= base + (ATA_REG_LBAL << 1) + 1;
		ap->ioaddr.lbam_addr	= base + (ATA_REG_LBAM << 1) + 1;
		ap->ioaddr.lbah_addr	= base + (ATA_REG_LBAH << 1) + 1;
		ap->ioaddr.device_addr	= base + (ATA_REG_DEVICE << 1) + 1;
		ap->ioaddr.status_addr	= base + (ATA_REG_STATUS << 1) + 1;
		ap->ioaddr.command_addr	= base + (ATA_REG_CMD << 1) + 1;
		ap->ioaddr.altstatus_addr = cs1 + (6 << 1) + 1;
		ap->ioaddr.ctl_addr	= cs1 + (6 << 1) + 1;
		octeon_cf_ops.sff_data_xfer = octeon_cf_data_xfer16;

		ap->mwdma_mask	= enable_dma ? ATA_MWDMA4 : 0;

		/* True IDE mode needs a timer to poll for not-busy.  */
		hrtimer_init(&cf_port->delayed_finish, CLOCK_MONOTONIC,
			     HRTIMER_MODE_REL);
		cf_port->delayed_finish.function = octeon_cf_delayed_finish;
	} else {
		/* 16 bit but not True IDE */
		base = cs0 + 0x800;
		octeon_cf_ops.sff_data_xfer	= octeon_cf_data_xfer16;
		octeon_cf_ops.softreset		= octeon_cf_softreset16;
		octeon_cf_ops.sff_check_status	= octeon_cf_check_status16;
		octeon_cf_ops.sff_tf_read	= octeon_cf_tf_read16;
		octeon_cf_ops.sff_tf_load	= octeon_cf_tf_load16;
		octeon_cf_ops.sff_exec_command	= octeon_cf_exec_command16;

		ap->ioaddr.data_addr	= base + ATA_REG_DATA;
		ap->ioaddr.nsect_addr	= base + ATA_REG_NSECT;
		ap->ioaddr.lbal_addr	= base + ATA_REG_LBAL;
		ap->ioaddr.ctl_addr	= base + 0xe;
		ap->ioaddr.altstatus_addr = base + 0xe;
	}
	cf_port->c0 = ap->ioaddr.ctl_addr;

	rv = dma_coerce_mask_and_coherent(&pdev->dev, DMA_BIT_MASK(64));
	if (rv)
		return rv;

	ata_port_desc(ap, "cmd %p ctl %p", base, ap->ioaddr.ctl_addr);

	dev_info(&pdev->dev, "version " DRV_VERSION" %d bit%s.\n",
		 is_16bit ? 16 : 8,
		 cf_port->is_true_ide ? ", True IDE" : "");

	return ata_host_activate(host, irq, irq_handler,
				 IRQF_SHARED, &octeon_cf_sht);
}
