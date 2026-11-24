/* QLM seed slice: drivers/mtd/maps/physmap-core.c @ 620b90d30c08^ (buggy).
 * Function text below the preamble is verbatim from the kernel tree. */
#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

#define EINVAL 22

struct device;
struct mtd_info;
struct map_info;

struct platform_device {
    struct {
        void *platform_data;
        void *driver_data;
    } dev;
};

struct physmap_flash_info {
    struct mtd_info *cmtd;
    struct mtd_info **mtds;
    int nmaps;
};

struct physmap_flash_data {
    void (*exit)(struct platform_device *dev);
};

extern void *platform_get_drvdata(const struct platform_device *pdev);
extern int mtd_device_unregister(struct mtd_info *mtd);
extern void mtd_concat_destroy(struct mtd_info *mtd);
extern void map_destroy(struct mtd_info *mtd);
extern void *dev_get_platdata(const void *dev);
extern int pm_runtime_put(void *dev);
extern int pm_runtime_disable(void *dev);

/* ---- verbatim kernel code ---- */
static int physmap_flash_remove(struct platform_device *dev)
{
	struct physmap_flash_info *info;
	struct physmap_flash_data *physmap_data;
	int i, err = 0;

	info = platform_get_drvdata(dev);
	if (!info)
		goto out;

	if (info->cmtd) {
		err = mtd_device_unregister(info->cmtd);
		if (err)
			goto out;

		if (info->cmtd != info->mtds[0])
			mtd_concat_destroy(info->cmtd);
	}

	for (i = 0; i < info->nmaps; i++) {
		if (info->mtds[i])
			map_destroy(info->mtds[i]);
	}

	physmap_data = dev_get_platdata(&dev->dev);
	if (physmap_data && physmap_data->exit)
		physmap_data->exit(dev);

out:
	pm_runtime_put(&dev->dev);
	pm_runtime_disable(&dev->dev);
	return err;
}
