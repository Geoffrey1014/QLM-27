/* QLM seed slice: drivers/hsi/controllers/omap_ssi_core.c @ 9a2ea132df86 (fixed).
 * Function text below the preamble is verbatim from the kernel tree. */
#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

#define GFP_KERNEL 0
#define EINVAL 22
#define ENOMEM 12
#define ENODEV 19

struct device_node;

struct device {
	struct device_node *of_node;
};

struct platform_device {
	struct device dev;
};

struct hsi_controller {
	int id;
};

extern int dev_err(const struct device *dev, const char *fmt, ...);
extern int dev_info(const struct device *dev, const char *fmt, ...);

extern int ssi_of_get_available_ports_count(const struct device_node *np);
extern struct hsi_controller *hsi_alloc_controller(int n_ports, int flags);
extern void platform_set_drvdata(struct platform_device *pdev, void *data);
extern int ssi_add_controller(struct hsi_controller *ssi, struct platform_device *pd);
extern void pm_runtime_enable(struct device *dev);
extern void pm_runtime_disable(struct device *dev);
extern int ssi_hw_init(struct hsi_controller *ssi);
extern int ssi_debug_add_ctrl(struct hsi_controller *ssi);
extern bool of_device_is_compatible(const struct device_node *device, const char *compat);
extern struct platform_device *of_platform_device_create(struct device_node *np, const char *bus_id, struct device *parent);
extern int device_for_each_child(struct device *parent, void *data, int (*fn)(struct device *dev, void *data));
extern int ssi_remove_ports(struct device *dev, void *c);
extern void ssi_remove_controller(struct hsi_controller *ssi);
extern void of_node_put(struct device_node *node);

#define for_each_available_child_of_node(parent, child) \
	for ((child) = (struct device_node *)0; (child); (child) = (struct device_node *)0)
#undef CONFIG_DEBUG_FS
#define CONFIG_DEBUG_FS 1

/* ---- verbatim kernel code ---- */
static int ssi_probe(struct platform_device *pd)
{
	struct platform_device *childpdev;
	struct device_node *np = pd->dev.of_node;
	struct device_node *child;
	struct hsi_controller *ssi;
	int err;
	int num_ports;

	if (!np) {
		dev_err(&pd->dev, "missing device tree data\n");
		return -EINVAL;
	}

	num_ports = ssi_of_get_available_ports_count(np);

	ssi = hsi_alloc_controller(num_ports, GFP_KERNEL);
	if (!ssi) {
		dev_err(&pd->dev, "No memory for controller\n");
		return -ENOMEM;
	}

	platform_set_drvdata(pd, ssi);

	err = ssi_add_controller(ssi, pd);
	if (err < 0)
		goto out1;

	pm_runtime_enable(&pd->dev);

	err = ssi_hw_init(ssi);
	if (err < 0)
		goto out2;
#ifdef CONFIG_DEBUG_FS
	err = ssi_debug_add_ctrl(ssi);
	if (err < 0)
		goto out2;
#endif

	for_each_available_child_of_node(np, child) {
		if (!of_device_is_compatible(child, "ti,omap3-ssi-port"))
			continue;

		childpdev = of_platform_device_create(child, NULL, &pd->dev);
		if (!childpdev) {
			err = -ENODEV;
			dev_err(&pd->dev, "failed to create ssi controller port\n");
			of_node_put(child);
			goto out3;
		}
	}

	dev_info(&pd->dev, "ssi controller %d initialized (%d ports)!\n",
		ssi->id, num_ports);
	return err;
out3:
	device_for_each_child(&pd->dev, NULL, ssi_remove_ports);
out2:
	ssi_remove_controller(ssi);
out1:
	platform_set_drvdata(pd, NULL);
	pm_runtime_disable(&pd->dev);

	return err;
}
