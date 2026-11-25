/*
 * POC for Linux Kernel Bug: Refcount Leak in of_find_compatible_node
 * Patch Commit: 0f83e6b4161617014017a694888dd8743f46f071
 *
 * Bug Description:
 * In omap_gic_of_init(), of_find_compatible_node() is called twice to find
 * device tree nodes for GIC and TWD timer. The function returns node pointers
 * with incremented refcounts, but of_node_put() is never called to release
 * them, causing reference count leaks.
 *
 * Bug Pattern (CWE-911: Improper Update of Reference Count):
 *   Target API: of_find_compatible_node()
 *   Post-operation: of_node_put()
 *   Critical variable: np (struct device_node*)
 *   Path conditions: All paths after using the node - unconditional leak
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <stdatomic.h>

/*
 * Simulated device_node structure with reference counting
 */
struct device_node {
    char name[64];
    char compatible[64];
    atomic_int refcount;
    struct device_node *next;  /* For linked list of nodes */
};

/* Simulated device tree - global list of nodes */
static struct device_node *device_tree = NULL;

/* Global tracking for leak detection */
static int total_gets = 0;
static int total_puts = 0;

/*
 * Simulated of_node_get() - increments reference count
 */
static struct device_node *of_node_get(struct device_node *node)
{
    if (node) {
        atomic_fetch_add(&node->refcount, 1);
        total_gets++;
        printf("  [REFCOUNT] of_node_get(%s): refcount now %d\n",
               node->name, atomic_load(&node->refcount));
    }
    return node;
}

/*
 * Simulated of_node_put() - decrements reference count
 */
static void of_node_put(struct device_node *node)
{
    if (node) {
        atomic_fetch_sub(&node->refcount, 1);
        total_puts++;
        printf("  [REFCOUNT] of_node_put(%s): refcount now %d\n",
               node->name, atomic_load(&node->refcount));
    }
}

/*
 * Simulated of_find_compatible_node()
 * Returns a node with incremented refcount - caller must call of_node_put()
 */
static struct device_node *of_find_compatible_node(
    struct device_node *from,
    const char *type,
    const char *compatible)
{
    struct device_node *node;
    (void)from;  /* Unused in this simulation */
    (void)type;  /* Unused in this simulation */

    for (node = device_tree; node; node = node->next) {
        if (strcmp(node->compatible, compatible) == 0) {
            printf("  [FIND] Found node '%s' matching '%s'\n",
                   node->name, compatible);
            return of_node_get(node);  /* Returns with incremented refcount */
        }
    }
    return NULL;
}

/*
 * Simulated of_iomap() - maps device registers
 */
static void *of_iomap(struct device_node *np, int index)
{
    (void)index;
    if (np) {
        printf("  [IOMAP] Mapping registers for '%s'\n", np->name);
        return (void *)0xDEADBEEF;  /* Fake address */
    }
    return NULL;
}

/*
 * BUGGY version: Missing of_node_put() after of_find_compatible_node()
 * This mirrors the original vulnerable code in omap_gic_of_init()
 */
static void init_buggy(void)
{
    struct device_node *np;
    void *gic_dist_base_addr;
    void *twd_base;

    printf("\n--- BUGGY init() ---\n");

    /* Bug 1: of_find_compatible_node returns node with refcount+1 */
    np = of_find_compatible_node(NULL, NULL, "arm,cortex-a9-gic");
    gic_dist_base_addr = of_iomap(np, 0);
    /* BUG: Missing of_node_put(np) here! */
    if (!gic_dist_base_addr)
        printf("  [WARN] gic_dist_base_addr is NULL\n");

    /* Bug 2: Same pattern - missing of_node_put() */
    np = of_find_compatible_node(NULL, NULL, "arm,cortex-a9-twd-timer");
    twd_base = of_iomap(np, 0);
    /* BUG: Missing of_node_put(np) here! */
    if (!twd_base)
        printf("  [WARN] twd_base is NULL\n");

    printf("  init_buggy() completed\n");
}

/*
 * FIXED version: Properly calls of_node_put() after using the node
 */
static void init_fixed(void)
{
    struct device_node *np;
    void *gic_dist_base_addr;
    void *twd_base;

    printf("\n--- FIXED init() ---\n");

    np = of_find_compatible_node(NULL, NULL, "arm,cortex-a9-gic");
    gic_dist_base_addr = of_iomap(np, 0);
    of_node_put(np);  /* FIX: Release reference after use */
    if (!gic_dist_base_addr)
        printf("  [WARN] gic_dist_base_addr is NULL\n");

    np = of_find_compatible_node(NULL, NULL, "arm,cortex-a9-twd-timer");
    twd_base = of_iomap(np, 0);
    of_node_put(np);  /* FIX: Release reference after use */
    if (!twd_base)
        printf("  [WARN] twd_base is NULL\n");

    printf("  init_fixed() completed\n");
}

/*
 * Create simulated device tree for testing
 */
static void create_device_tree(void)
{
    struct device_node *gic = calloc(1, sizeof(*gic));
    struct device_node *twd = calloc(1, sizeof(*twd));
    struct device_node *uart = calloc(1, sizeof(*uart));

    strcpy(gic->name, "gic@48241000");
    strcpy(gic->compatible, "arm,cortex-a9-gic");
    atomic_init(&gic->refcount, 1);

    strcpy(twd->name, "timer@48240600");
    strcpy(twd->compatible, "arm,cortex-a9-twd-timer");
    atomic_init(&twd->refcount, 1);

    strcpy(uart->name, "serial@4806a000");
    strcpy(uart->compatible, "ti,omap4-uart");
    atomic_init(&uart->refcount, 1);

    /* Build linked list */
    gic->next = twd;
    twd->next = uart;
    uart->next = NULL;

    device_tree = gic;
}

/*
 * Check for refcount leaks in device tree
 */
static void check_refcount_leaks(void)
{
    struct device_node *node;
    int leaked_nodes = 0;

    printf("\n--- Refcount Status ---\n");
    for (node = device_tree; node; node = node->next) {
        int ref = atomic_load(&node->refcount);
        printf("  %s: refcount = %d %s\n",
               node->name, ref,
               ref > 1 ? "[LEAKED!]" : "[OK]");
        if (ref > 1)
            leaked_nodes++;
    }

    printf("\n--- Summary ---\n");
    printf("  Total of_node_get() calls: %d\n", total_gets);
    printf("  Total of_node_put() calls: %d\n", total_puts);
    printf("  Leaked references: %d\n", total_gets - total_puts);
    printf("  Nodes with leaked refcount: %d\n", leaked_nodes);
}

/*
 * Free device tree
 */
static void free_device_tree(void)
{
    struct device_node *node = device_tree;
    while (node) {
        struct device_node *next = node->next;
        free(node);
        node = next;
    }
    device_tree = NULL;
}

int main(void)
{
    printf("=== POC: Linux Kernel Refcount Leak Bug ===\n");
    printf("Commit: 0f83e6b4161617014017a694888dd8743f46f071\n");
    printf("Bug: Missing of_node_put() after of_find_compatible_node()\n");

    /* Test BUGGY version */
    printf("\n========== Testing BUGGY Version ==========\n");
    create_device_tree();
    total_gets = 0;
    total_puts = 0;

    init_buggy();
    check_refcount_leaks();

    if (total_gets != total_puts) {
        printf("\n[BUG CONFIRMED] Refcount leak detected!\n");
        printf("  The nodes returned by of_find_compatible_node() were not released.\n");
    }

    free_device_tree();

    /* Test FIXED version */
    printf("\n\n========== Testing FIXED Version ==========\n");
    create_device_tree();
    total_gets = 0;
    total_puts = 0;

    init_fixed();
    check_refcount_leaks();

    if (total_gets == total_puts) {
        printf("\n[FIX VERIFIED] No refcount leak in fixed version.\n");
        printf("  All nodes are properly released with of_node_put().\n");
    }

    free_device_tree();

    /* Print bug pattern analysis */
    printf("\n\n=== Bug Pattern Analysis ===\n");
    printf("Bug Type: CWE-911 (Improper Update of Reference Count)\n\n");
    printf("Four-Features Pattern:\n");
    printf("  Target API: of_find_compatible_node()\n");
    printf("              (also: of_find_node_by_name, of_find_node_by_path, etc.)\n");
    printf("  Post-operation: of_node_put()\n");
    printf("  Critical variable: np (struct device_node*)\n");
    printf("  Path condition: All paths after using the node (unconditional)\n\n");
    printf("Fix: Call of_node_put(np) after the node is no longer needed.\n");

    return 0;
}
