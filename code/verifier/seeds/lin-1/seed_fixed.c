/* QLM seed slice: arch/arm/mach-omap2/pm33xx-core.c @ 74139a64e8ce (fixed).
 * Function text below the preamble is verbatim from the kernel tree. */
#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>

#define __init
#define CPUIDLE_STATE_MAX 10
#define WFI_FLAG_WAKE_M3        (1 << 0)
#define WFI_FLAG_FLUSH_CACHE    (1 << 1)
#define GFP_KERNEL 0
#define ENOMEM 12

#define pr_warn(fmt, ...) do { } while (0)

struct device_node;

struct amx3_idle_state {
    int wfi_flags;
};

extern struct amx3_idle_state *idle_states;

extern struct device_node *of_parse_phandle(const struct device_node *np,
                                            const char *phandle_name,
                                            int index);
extern bool of_device_is_available(const struct device_node *device);
extern void of_node_put(struct device_node *node);
extern bool of_property_read_bool(const struct device_node *np,
                                  const char *propname);
extern void *kcalloc(size_t n, size_t size, unsigned int flags);

/* ---- verbatim kernel code ---- */
static int __init amx3_idle_init(struct device_node *cpu_node, int cpu)
{
	struct device_node *state_node;
	struct amx3_idle_state states[CPUIDLE_STATE_MAX];
	int i;
	int state_count = 1;

	for (i = 0; ; i++) {
		state_node = of_parse_phandle(cpu_node, "cpu-idle-states", i);
		if (!state_node)
			break;

		if (!of_device_is_available(state_node)) {
			of_node_put(state_node);
			continue;
		}

		if (i == CPUIDLE_STATE_MAX) {
			pr_warn("%s: cpuidle states reached max possible\n",
				__func__);
			of_node_put(state_node);
			break;
		}

		states[state_count].wfi_flags = 0;

		if (of_property_read_bool(state_node, "ti,idle-wkup-m3"))
			states[state_count].wfi_flags |= WFI_FLAG_WAKE_M3 |
							 WFI_FLAG_FLUSH_CACHE;

		of_node_put(state_node);
		state_count++;
	}

	idle_states = kcalloc(state_count, sizeof(*idle_states), GFP_KERNEL);
	if (!idle_states)
		return -ENOMEM;

	for (i = 1; i < state_count; i++)
		idle_states[i].wfi_flags = states[i].wfi_flags;

	return 0;
}
