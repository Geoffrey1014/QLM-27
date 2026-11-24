/* QLM seed slice: sound/soc/rockchip/rockchip_pdm.c @ f141a422159a (fixed).
 * Function text below the preamble is verbatim from the kernel tree. */
#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

struct device;
struct regmap;

struct rk_pdm_dev {
    struct regmap *regmap;
};

extern void *dev_get_drvdata(const struct device *dev);
extern int pm_runtime_get_sync(struct device *dev);
extern int pm_runtime_put(struct device *dev);
extern int regcache_sync(struct regmap *map);

/* ---- verbatim kernel code ---- */
static int rockchip_pdm_resume(struct device *dev)
{
	struct rk_pdm_dev *pdm = dev_get_drvdata(dev);
	int ret;

	ret = pm_runtime_get_sync(dev);
	if (ret < 0) {
		pm_runtime_put(dev);
		return ret;
	}

	ret = regcache_sync(pdm->regmap);

	pm_runtime_put(dev);

	return ret;
}
