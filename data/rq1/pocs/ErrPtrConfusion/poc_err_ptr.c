/*
 * PoC for the "ERR_PTR / IS_ERR confusion" pattern (error-pointer dereference).
 *
 * Mirrors the shapes of the ground-truth fixes:
 *   5edb7338d611  serial: 8250: loongson: Fix NULL vs IS_ERR() bug in probe
 *                 (devm_platform_get_and_ioremap_resource() returns ERR_PTR, caller
 *                  checked `if (!p)` -> shape A, wrong guard)
 *   cda5dc12eb12, fc33bf0e097c  (same NULL-vs-IS_ERR family)
 *
 * And the in-tree findings it must flag (RQ1 #47, #48):
 *   drivers/mtd/nand/raw/nand_toshiba.c::toshiba_nand_benand_read_eccstatus_op
 *     (sdr = nand_get_sdr_timings(...); sdr->tADL_min, no guard -> shape B)
 *   drivers/thermal/ti-soc-thermal/ti-thermal-common.c::ti_thermal_report_sensor_temperature
 *     (data = ti_bandgap_get_sensor_data(...); data->thermal_wq, no guard -> shape B)
 *
 * *_buggy : error pointer dereferenced without a dominating IS_ERR guard -> MUST be flagged.
 * *_fixed : IS_ERR-guarded, or reassigned on the error path              -> MUST be spared.
 */
#include <stddef.h>

#define MAX_ERRNO 4095
#define ENOMEM 12
#define EINVAL 22
#define ENODEV 19
#define unlikely(x) (x)

/* ---- minimal kernel fakes: ERR_PTR helpers as real functions ---- */
static inline void *ERR_PTR(long error) { return (void *)error; }
static inline long PTR_ERR(const void *ptr) { return (long)ptr; }
static inline int IS_ERR(const void *ptr)
{
	return unlikely((unsigned long)ptr >= (unsigned long)-MAX_ERRNO);
}
static inline int IS_ERR_OR_NULL(const void *ptr)
{
	return !ptr || IS_ERR(ptr);
}

/* ---- producer 1: ioremap-style resource getter (seed 5edb7338d611) ---- */
struct resource {
	unsigned long start;
	unsigned long end;
};

struct platform_device {
	int id;
	struct resource *res;
	int nres;
};

struct iomem_region {
	unsigned int reg_ctrl;
	unsigned int reg_data;
};

struct iomem_region *devm_platform_get_and_ioremap_resource(struct platform_device *pdev,
							    unsigned int index,
							    struct resource **res)
{
	if (index >= (unsigned int)pdev->nres)
		return ERR_PTR(-EINVAL);
	*res = &pdev->res[index];
	return (struct iomem_region *)(*res)->start;
}

/* ---- producer 2: timings getter (finding #47, nand_toshiba) ---- */
struct nand_sdr_timings {
	unsigned int tADL_min;
	unsigned int tWHR_min;
};

struct nand_chip {
	int iface_type;
	struct nand_sdr_timings sdr;
};

const struct nand_sdr_timings *nand_get_sdr_timings(struct nand_chip *chip)
{
	if (chip->iface_type != 0)
		return ERR_PTR(-EINVAL);
	return &chip->sdr;
}

/* ---- producer 3: sensor-data getter (finding #48, ti-thermal) ---- */
struct sensor_data {
	int thermal_wq;
	int last_temp;
};

struct bandgap {
	int nsensors;
	struct sensor_data *data;
};

struct sensor_data *ti_bandgap_get_sensor_data(struct bandgap *bgp, int id)
{
	if (id < 0 || id >= bgp->nsensors)
		return ERR_PTR(-ENODEV);
	return &bgp->data[id];
}

/* ================================================================== *
 *  BUG cases
 * ================================================================== */

/* Shape A (seed 5edb7338d611): NULL check where IS_ERR is needed. */
int wrong_guard_probe_buggy(struct platform_device *pdev)
{
	struct resource *res;
	struct iomem_region *base;

	base = devm_platform_get_and_ioremap_resource(pdev, 0, &res);
	if (!base)
		return -ENOMEM;

	return base->reg_ctrl;		/* ERR_PTR slips past `!base` */
}

/* Shape A variant: explicit `== NULL`. */
int wrong_guard_eq_null_buggy(struct platform_device *pdev)
{
	struct resource *res;
	struct iomem_region *base;

	base = devm_platform_get_and_ioremap_resource(pdev, 1, &res);
	if (base == NULL)
		return -ENOMEM;

	base->reg_data = 1;
	return 0;
}

/* Shape B (finding #47): no guard at all. */
int unchecked_timings_buggy(struct nand_chip *chip)
{
	const struct nand_sdr_timings *sdr;

	sdr = nand_get_sdr_timings(chip);
	return sdr->tADL_min / 1000;
}

/* Shape B (finding #48): no guard at all. */
void unchecked_sensor_buggy(struct bandgap *bgp, int id, int temp)
{
	struct sensor_data *data;

	data = ti_bandgap_get_sensor_data(bgp, id);
	data->thermal_wq = temp;
}

/* ================================================================== *
 *  SAFE cases
 * ================================================================== */

/* The fixed version of the seed: IS_ERR guard dominates the deref. */
int is_err_probe_fixed(struct platform_device *pdev)
{
	struct resource *res;
	struct iomem_region *base;

	base = devm_platform_get_and_ioremap_resource(pdev, 0, &res);
	if (IS_ERR(base))
		return PTR_ERR(base);

	return base->reg_ctrl;
}

/* IS_ERR_OR_NULL guard. */
int is_err_or_null_fixed(struct nand_chip *chip)
{
	const struct nand_sdr_timings *sdr;

	sdr = nand_get_sdr_timings(chip);
	if (IS_ERR_OR_NULL(sdr))
		return -EINVAL;

	return sdr->tWHR_min;
}

/* Error path reassigns the variable before use (SSA kills the producer def). */
void reassign_on_error_fixed(struct bandgap *bgp, int id, struct sensor_data *fallback)
{
	struct sensor_data *data;

	data = ti_bandgap_get_sensor_data(bgp, id);
	if (IS_ERR(data))
		data = fallback;

	data->last_temp = 0;
}
