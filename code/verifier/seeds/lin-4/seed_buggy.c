/* QLM seed slice: drivers/memory/samsung/exynos5422-dmc.c @ 1332661e0930^ (buggy).
 * Function text below the preamble is verbatim from the kernel tree. */
#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

typedef unsigned int u32;
typedef unsigned long gfp_t;

#define GFP_KERNEL ((gfp_t)0)
#define EINVAL 22
#define ENOMEM 12
#define TIMING_COUNT 4
#define DDR_TYPE_LPDDR3 1

struct device_node;
struct device;

struct dmc_opp_table {
    u32 freq_hz;
    u32 volt_uv;
};

struct lpddr3_timings;
struct lpddr3_min_tck;

struct exynos5_dmc {
    struct device *dev;
    u32 *timing_row;
    u32 *timing_data;
    u32 *timing_power;
    struct lpddr3_timings *timings;
    struct lpddr3_min_tck *min_tck;
    int timings_arr_size;
    struct dmc_opp_table *opp;
    int opp_count;
    u32 bypass_timing_row;
    u32 bypass_timing_data;
    u32 bypass_timing_power;
};

extern struct device_node *of_parse_phandle(const struct device_node *np,
                                            const char *phandle_name,
                                            int index);
extern void of_node_put(struct device_node *node);
extern void dev_warn(const struct device *dev, const char *fmt, ...);
extern void *devm_kmalloc_array(struct device *dev, size_t n, size_t size, gfp_t flags);
extern struct lpddr3_timings *of_lpddr3_get_ddr_timings(struct device_node *np_ddr,
                                                       struct device *dev,
                                                       u32 ddr_type,
                                                       int *nr_frequencies);
extern struct lpddr3_min_tck *of_lpddr3_get_min_tck(struct device_node *np,
                                                   struct device *dev);
extern int create_timings_aligned(struct exynos5_dmc *dmc, u32 *reg_timing_row,
                                  u32 *reg_timing_data, u32 *reg_timing_power,
                                  u32 clk_period_ps);

#define dmc_dev_of_node(dmc) ((dmc)->dev->of_node)

/* Access dev->of_node through a forward-declared struct device below */
struct device {
    struct device_node *of_node;
};

/* ---- verbatim kernel code ---- */
static int of_get_dram_timings(struct exynos5_dmc *dmc)
{
	int ret = 0;
	int idx;
	struct device_node *np_ddr;
	u32 freq_mhz, clk_period_ps;

	np_ddr = of_parse_phandle(dmc->dev->of_node, "device-handle", 0);
	if (!np_ddr) {
		dev_warn(dmc->dev, "could not find 'device-handle' in DT\n");
		return -EINVAL;
	}

	dmc->timing_row = devm_kmalloc_array(dmc->dev, TIMING_COUNT,
					     sizeof(u32), GFP_KERNEL);
	if (!dmc->timing_row)
		return -ENOMEM;

	dmc->timing_data = devm_kmalloc_array(dmc->dev, TIMING_COUNT,
					      sizeof(u32), GFP_KERNEL);
	if (!dmc->timing_data)
		return -ENOMEM;

	dmc->timing_power = devm_kmalloc_array(dmc->dev, TIMING_COUNT,
					       sizeof(u32), GFP_KERNEL);
	if (!dmc->timing_power)
		return -ENOMEM;

	dmc->timings = of_lpddr3_get_ddr_timings(np_ddr, dmc->dev,
						 DDR_TYPE_LPDDR3,
						 &dmc->timings_arr_size);
	if (!dmc->timings) {
		of_node_put(np_ddr);
		dev_warn(dmc->dev, "could not get timings from DT\n");
		return -EINVAL;
	}

	dmc->min_tck = of_lpddr3_get_min_tck(np_ddr, dmc->dev);
	if (!dmc->min_tck) {
		of_node_put(np_ddr);
		dev_warn(dmc->dev, "could not get tck from DT\n");
		return -EINVAL;
	}

	/* Sorted array of OPPs with frequency ascending */
	for (idx = 0; idx < dmc->opp_count; idx++) {
		freq_mhz = dmc->opp[idx].freq_hz / 1000000;
		clk_period_ps = 1000000 / freq_mhz;

		ret = create_timings_aligned(dmc, &dmc->timing_row[idx],
					     &dmc->timing_data[idx],
					     &dmc->timing_power[idx],
					     clk_period_ps);
	}

	of_node_put(np_ddr);

	/* Take the highest frequency's timings as 'bypass' */
	dmc->bypass_timing_row = dmc->timing_row[idx - 1];
	dmc->bypass_timing_data = dmc->timing_data[idx - 1];
	dmc->bypass_timing_power = dmc->timing_power[idx - 1];

	return ret;
}
