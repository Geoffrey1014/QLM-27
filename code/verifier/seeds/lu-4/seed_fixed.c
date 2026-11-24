/* QLM seed slice: drivers/usb/dwc3/dwc3-pci.c @ 9bbfceea12a8 (fixed).
 * Function text below the preamble is verbatim from the kernel tree. */
#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

typedef unsigned long resource_size_t;
typedef unsigned int gfp_t;

#define GFP_KERNEL ((gfp_t)0)
#define ENODEV 19
#define ENOMEM 12
#define PLATFORM_DEVID_AUTO (-2)
#define IORESOURCE_MEM 0x00000200
#define IORESOURCE_IRQ 0x00000400
#define ARRAY_SIZE(a) (sizeof(a)/sizeof((a)[0]))

struct device;
struct fwnode_handle;
struct acpi_device;
struct property_entry;
struct platform_device;
struct pci_dev;

struct resource {
    resource_size_t start;
    resource_size_t end;
    const char *name;
    unsigned long flags;
};

struct work_struct {
    unsigned long data;
    void *entry_next;
    void *entry_prev;
    void (*func)(struct work_struct *);
};

struct device {
    struct device *parent;
    void *driver_data;
    struct fwnode_handle *fwnode;
};

struct platform_device {
    const char *name;
    int id;
    struct device dev;
};

struct pci_dev {
    unsigned int irq;
    struct device dev;
};

struct pci_device_id {
    unsigned long driver_data;
};

struct dwc3_pci {
    struct pci_dev *pci;
    struct platform_device *dwc3;
    struct work_struct wakeup_work;
};

extern int pcim_enable_device(struct pci_dev *pdev);
extern void pci_set_master(struct pci_dev *dev);
extern void *devm_kzalloc(struct device *dev, size_t size, gfp_t gfp);
extern struct platform_device *platform_device_alloc(const char *name, int id);
extern void *memset(void *s, int c, size_t n);
extern resource_size_t pci_resource_start(struct pci_dev *dev, int bar);
extern resource_size_t pci_resource_end(struct pci_dev *dev, int bar);
extern int platform_device_add_resources(struct platform_device *pdev,
                                         const struct resource *res,
                                         unsigned int num);
extern int platform_device_add_properties(struct platform_device *pdev,
                                          const struct property_entry *properties);
extern int dwc3_pci_quirks(struct dwc3_pci *dwc);
extern int platform_device_add(struct platform_device *pdev);
extern int device_init_wakeup(struct device *dev, bool enable);
extern void pci_set_drvdata(struct pci_dev *pdev, void *data);
extern void pm_runtime_put(struct device *dev);
extern void platform_device_put(struct platform_device *pdev);
extern int dev_err(const struct device *dev, const char *fmt, ...);
extern void dwc3_pci_resume_work(struct work_struct *work);
extern struct acpi_device *acpi_companion_get(struct device *dev);
extern void acpi_companion_set(struct device *dev, struct acpi_device *adev);

#define ACPI_COMPANION(dev) acpi_companion_get(dev)
#define ACPI_COMPANION_SET(dev, adev) acpi_companion_set((dev), (adev))
#define INIT_WORK(_work, _func) do { (_work)->func = (_func); } while (0)
#undef CONFIG_PM
#define CONFIG_PM 1

/* ---- verbatim kernel code ---- */
static int dwc3_pci_probe(struct pci_dev *pci, const struct pci_device_id *id)
{
	struct property_entry *p = (struct property_entry *)id->driver_data;
	struct dwc3_pci		*dwc;
	struct resource		res[2];
	int			ret;
	struct device		*dev = &pci->dev;

	ret = pcim_enable_device(pci);
	if (ret) {
		dev_err(dev, "failed to enable pci device\n");
		return -ENODEV;
	}

	pci_set_master(pci);

	dwc = devm_kzalloc(dev, sizeof(*dwc), GFP_KERNEL);
	if (!dwc)
		return -ENOMEM;

	dwc->dwc3 = platform_device_alloc("dwc3", PLATFORM_DEVID_AUTO);
	if (!dwc->dwc3)
		return -ENOMEM;

	memset(res, 0x00, sizeof(struct resource) * ARRAY_SIZE(res));

	res[0].start	= pci_resource_start(pci, 0);
	res[0].end	= pci_resource_end(pci, 0);
	res[0].name	= "dwc_usb3";
	res[0].flags	= IORESOURCE_MEM;

	res[1].start	= pci->irq;
	res[1].name	= "dwc_usb3";
	res[1].flags	= IORESOURCE_IRQ;

	ret = platform_device_add_resources(dwc->dwc3, res, ARRAY_SIZE(res));
	if (ret) {
		dev_err(dev, "couldn't add resources to dwc3 device\n");
		goto err;
	}

	dwc->pci = pci;
	dwc->dwc3->dev.parent = dev;
	ACPI_COMPANION_SET(&dwc->dwc3->dev, ACPI_COMPANION(dev));

	ret = platform_device_add_properties(dwc->dwc3, p);
	if (ret < 0)
		goto err;

	ret = dwc3_pci_quirks(dwc);
	if (ret)
		goto err;

	ret = platform_device_add(dwc->dwc3);
	if (ret) {
		dev_err(dev, "failed to register dwc3 device\n");
		goto err;
	}

	device_init_wakeup(dev, true);
	pci_set_drvdata(pci, dwc);
	pm_runtime_put(dev);
#ifdef CONFIG_PM
	INIT_WORK(&dwc->wakeup_work, dwc3_pci_resume_work);
#endif

	return 0;
err:
	platform_device_put(dwc->dwc3);
	return ret;
}
