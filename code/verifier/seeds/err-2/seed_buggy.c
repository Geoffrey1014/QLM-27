/* QLM seed slice: drivers/thermal/thermal_of.c @ 45c7eaeb29d6^ (buggy).
 * Function text below the preamble is verbatim from the kernel tree. */
#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

typedef unsigned int u32;
typedef unsigned long gfp_t;

#define GFP_KERNEL ((gfp_t)0)
#define ENODEV 19
#define ENOENT 2
#define ENOMEM 12
#define THERMAL_WEIGHT_DEFAULT 0

#define MAX_PHANDLE_ARGS 16

struct device_node;

struct of_phandle_args {
    struct device_node *np;
    int args_count;
    u32 args[MAX_PHANDLE_ARGS];
};

struct thermal_trip {
    struct device_node *np;
};

struct __thermal_cooling_bind_param {
    struct device_node *cooling_device;
    unsigned long min;
    unsigned long max;
};

struct __thermal_bind_params {
    struct __thermal_cooling_bind_param *tcbp;
    int count;
    int trip_id;
    unsigned int usage;
};

extern int of_property_read_u32(const struct device_node *np, const char *propname, u32 *out_value);
extern struct device_node *of_parse_phandle(const struct device_node *np, const char *phandle_name, int index);
extern int of_count_phandle_with_args(const struct device_node *np, const char *list_name, const char *cells_name);
extern int of_parse_phandle_with_args(const struct device_node *np, const char *list_name, const char *cells_name, int index, struct of_phandle_args *out_args);
extern void of_node_put(struct device_node *node);

extern void *kcalloc(size_t n, size_t size, gfp_t flags);
extern void kfree(const void *objp);

extern int pr_err(const char *fmt, ...);

/* ---- verbatim kernel code ---- */
static int thermal_of_populate_bind_params(struct device_node *np,
					   struct __thermal_bind_params *__tbp,
					   struct thermal_trip *trips,
					   int ntrips)
{
	struct of_phandle_args cooling_spec;
	struct __thermal_cooling_bind_param *__tcbp;
	struct device_node *trip;
	int ret, i, count;
	u32 prop;

	/* Default weight. Usage is optional */
	__tbp->usage = THERMAL_WEIGHT_DEFAULT;
	ret = of_property_read_u32(np, "contribution", &prop);
	if (ret == 0)
		__tbp->usage = prop;

	trip = of_parse_phandle(np, "trip", 0);
	if (!trip) {
		pr_err("missing trip property\n");
		return -ENODEV;
	}

	/* match using device_node */
	for (i = 0; i < ntrips; i++)
		if (trip == trips[i].np) {
			__tbp->trip_id = i;
			break;
		}

	if (i == ntrips) {
		ret = -ENODEV;
		goto end;
	}

	count = of_count_phandle_with_args(np, "cooling-device",
					   "#cooling-cells");
	if (!count) {
		pr_err("Add a cooling_device property with at least one device\n");
		goto end;
	}

	__tcbp = kcalloc(count, sizeof(*__tcbp), GFP_KERNEL);
	if (!__tcbp)
		goto end;

	for (i = 0; i < count; i++) {
		ret = of_parse_phandle_with_args(np, "cooling-device",
				"#cooling-cells", i, &cooling_spec);
		if (ret < 0) {
			pr_err("Invalid cooling-device entry\n");
			goto free_tcbp;
		}

		__tcbp[i].cooling_device = cooling_spec.np;

		if (cooling_spec.args_count >= 2) { /* at least min and max */
			__tcbp[i].min = cooling_spec.args[0];
			__tcbp[i].max = cooling_spec.args[1];
		} else {
			pr_err("wrong reference to cooling device, missing limits\n");
		}
	}

	__tbp->tcbp = __tcbp;
	__tbp->count = count;

	goto end;

free_tcbp:
	for (i = i - 1; i >= 0; i--)
		of_node_put(__tcbp[i].cooling_device);
	kfree(__tcbp);
end:
	of_node_put(trip);

	return ret;
}
