// Proof-of-concept demonstrating device node reference count leak
// Bug: of_parse_phandle returns a device_node with incremented refcount
// that must be released with of_node_put in all code paths

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>

// Stub definitions for kernel types and macros
#define __init
#define __initdata
#define GFP_KERNEL 0
#define CPUIDLE_STATE_MAX 10

// Simulated device_node structure with reference count
struct device_node {
    const char *name;
    int refcount;
    bool available;
};

// Simulated idle state structure
struct amx3_idle_state {
    int wfi_flags;
};

#define WFI_FLAG_WAKE_M3    0x1
#define WFI_FLAG_FLUSH_CACHE 0x2

// Global tracking for demonstration
static int total_refcount_leaks = 0;

// Stub: of_parse_phandle - returns device_node with incremented refcount
static struct device_node *of_parse_phandle(const struct device_node *np,
                                            const char *phandle_name, int index)
{
    // Simulate returning NULL after a few iterations
    if (index >= 3)
        return NULL;
    
    // Allocate and return a device_node with refcount = 1
    struct device_node *node = malloc(sizeof(*node));
    if (node) {
        node->name = "idle-state";
        node->refcount = 1;  // Reference count incremented
        // Make index 1 unavailable for testing
        node->available = (index != 1);
        printf("  of_parse_phandle: allocated node %d, refcount=%d\n", 
               index, node->refcount);
    }
    return node;
}

// Stub: of_node_put - decrements reference count
static void of_node_put(struct device_node *node)
{
    if (node) {
        node->refcount--;
        printf("  of_node_put: decremented refcount to %d\n", node->refcount);
        if (node->refcount == 0) {
            printf("  of_node_put: freeing node\n");
            free(node);
        }
    }
}

// Stub: of_device_is_available
static bool of_device_is_available(const struct device_node *node)
{
    return node ? node->available : false;
}

// Stub: of_property_read_bool
static bool of_property_read_bool(const struct device_node *node, const char *prop)
{
    // Simulate some nodes having the property
    return true;
}

// Stub: kcalloc
static void *kcalloc(size_t n, size_t size, int flags)
{
    return calloc(n, size);
}

// Stub: pr_warn
#define pr_warn(fmt, ...) printf("WARNING: " fmt, ##__VA_ARGS__)

// ============================================================================
// BUGGY VERSION - Missing of_node_put in error paths
// ============================================================================
static int __init func_buggy(struct device_node *cpu_node, int cpu)
{
    struct device_node *state_node;
    struct amx3_idle_state states[CPUIDLE_STATE_MAX];
    struct amx3_idle_state *idle_states;
    int i;
    int state_count = 1;

    printf("=== BUGGY VERSION ===\n");

    for (i = 0; ; i++) {
        state_node = of_parse_phandle(cpu_node, "cpu-idle-states", i);
        if (!state_node)
            break;

        // BUG: Missing of_node_put before continue
        if (!of_device_is_available(state_node)) {
            printf("  Node %d not available, continuing WITHOUT of_node_put (LEAK!)\n", i);
            total_refcount_leaks++;
            continue;  // LEAK: state_node reference not released
        }

        // BUG: Missing of_node_put before break
        if (i == CPUIDLE_STATE_MAX) {
            pr_warn("%s: cpuidle states reached max possible\n", __func__);
            total_refcount_leaks++;
            break;  // LEAK: state_node reference not released
        }

        states[state_count].wfi_flags = 0;

        if (of_property_read_bool(state_node, "ti,idle-wkup-m3"))
            states[state_count].wfi_flags |= WFI_FLAG_WAKE_M3 |
                                             WFI_FLAG_FLUSH_CACHE;

        state_count++;
        // BUG: Missing of_node_put after normal processing
        printf("  Processed node %d WITHOUT of_node_put (LEAK!)\n", i);
        total_refcount_leaks++;
    }

    idle_states = kcalloc(state_count, sizeof(*idle_states), GFP_KERNEL);
    if (!idle_states)
        return -1;

    for (i = 1; i < state_count; i++)
        idle_states[i].wfi_flags = states[i].wfi_flags;

    free(idle_states);
    return 0;
}

// ============================================================================
// FIXED VERSION - Proper of_node_put in all paths
// ============================================================================
static int __init func_fixed(struct device_node *cpu_node, int cpu)
{
    struct device_node *state_node;
    struct amx3_idle_state states[CPUIDLE_STATE_MAX];
    struct amx3_idle_state *idle_states;
    int i;
    int state_count = 1;

    printf("\n=== FIXED VERSION ===\n");

    for (i = 0; ; i++) {
        state_node = of_parse_phandle(cpu_node, "cpu-idle-states", i);
        if (!state_node)
            break;

        // FIX: Call of_node_put before continue
        if (!of_device_is_available(state_node)) {
            printf("  Node %d not available, calling of_node_put before continue\n", i);
            of_node_put(state_node);
            continue;
        }

        // FIX: Call of_node_put before break
        if (i == CPUIDLE_STATE_MAX) {
            pr_warn("%s: cpuidle states reached max possible\n", __func__);
            of_node_put(state_node);
            break;
        }

        states[state_count].wfi_flags = 0;

        if (of_property_read_bool(state_node, "ti,idle-wkup-m3"))
            states[state_count].wfi_flags |= WFI_FLAG_WAKE_M3 |
                                             WFI_FLAG_FLUSH_CACHE;

        state_count++;
        
        // FIX: Call of_node_put after normal processing
        printf("  Processed node %d, calling of_node_put\n", i);
        of_node_put(state_node);
    }

    idle_states = kcalloc(state_count, sizeof(*idle_states), GFP_KERNEL);
    if (!idle_states)
        return -1;

    for (i = 1; i < state_count; i++)
        idle_states[i].wfi_flags = states[i].wfi_flags;

    free(idle_states);
    return 0;
}

int main(void)
{
    // Create a dummy cpu_node for testing
    struct device_node cpu_node = {
        .name = "cpu",
        .refcount = 1,
        .available = true
    };

    printf("Device Node Reference Count Leak POC\n");
    printf("=====================================\n\n");
    printf("This demonstrates CWE-401: Missing Release of Memory after Effective Lifetime\n");
    printf("Bug: of_parse_phandle() increments refcount, of_node_put() must be called\n\n");

    // Run buggy version
    total_refcount_leaks = 0;
    func_buggy(&cpu_node, 0);
    printf("\nBuggy version: %d reference count leaks\n", total_refcount_leaks);

    // Run fixed version
    func_fixed(&cpu_node, 0);
    printf("\nFixed version: All references properly released\n");

    return 0;
}