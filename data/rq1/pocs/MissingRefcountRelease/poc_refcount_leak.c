/*
 * POC for Linux Kernel Bug: Refcount Leak in for_each_available_child_of_node
 * Patch Commit: 9a2ea132df860177b33c9fd421b26c4e9a0a9396
 *
 * Bug Description:
 * In ssi_probe(), when iterating over child device tree nodes using
 * for_each_available_child_of_node(), if of_platform_device_create() fails,
 * the function exits early via 'goto out3' without calling of_node_put()
 * on the current child node, causing a reference count leak.
 *
 * Bug Pattern (CWE-911: Improper Update of Reference Count):
 *   Target API: for_each_available_child_of_node() / of_get_next_available_child()
 *   Post-operation: of_node_put()
 *   Critical variable: child (struct device_node*)
 *   Path conditions: early exit from loop (goto/break/return) without of_node_put()
 *
 * This POC simulates the kernel's device tree refcounting mechanism in userspace.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <stdatomic.h>

/*
 * Simulated device_node structure with reference counting
 * (mirrors Linux kernel's struct device_node)
 */
struct device_node {
    char name[64];
    atomic_int refcount;
    struct device_node *sibling;
    struct device_node *child;
    bool available;  /* simulates status = "okay" vs "disabled" */
};

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
 * Simulated of_get_next_available_child()
 * - Returns next available child node with incremented refcount
 * - Decrements refcount of previous node
 */
static struct device_node *of_get_next_available_child(
    const struct device_node *node,
    struct device_node *prev)
{
    struct device_node *next;

    if (!node)
        return NULL;

    next = prev ? prev->sibling : node->child;

    /* Find next available node */
    for (; next; next = next->sibling) {
        if (!next->available)
            continue;
        of_node_get(next);
        break;
    }

    /* Release reference on previous node */
    of_node_put(prev);

    return next;
}

/*
 * Simulated for_each_available_child_of_node macro
 */
#define for_each_available_child_of_node(parent, child) \
    for (child = of_get_next_available_child(parent, NULL); \
         child != NULL; \
         child = of_get_next_available_child(parent, child))

/*
 * Simulated of_platform_device_create()
 * Returns NULL to simulate failure on specific nodes
 */
static void *of_platform_device_create(struct device_node *child, int fail_on_third)
{
    static int call_count = 0;
    call_count++;

    if (fail_on_third && call_count >= 3) {
        printf("  [ERROR] of_platform_device_create(%s) FAILED!\n", child->name);
        return NULL;  /* Simulate failure */
    }

    printf("  [OK] of_platform_device_create(%s) succeeded\n", child->name);
    return (void *)1;  /* Non-NULL = success */
}

/*
 * BUGGY version: Missing of_node_put(child) on early exit
 * This mirrors the original vulnerable code in ssi_probe()
 */
static int probe_buggy(struct device_node *np)
{
    struct device_node *child;
    void *childpdev;
    int err = 0;

    printf("\n--- BUGGY probe() ---\n");

    for_each_available_child_of_node(np, child) {
        childpdev = of_platform_device_create(child, 1);
        if (!childpdev) {
            err = -1;
            printf("  [BUG] Early exit WITHOUT of_node_put(child)!\n");
            /* BUG: Missing of_node_put(child) here! */
            goto out_error;
        }
    }

    printf("  Probe completed successfully\n");
    return 0;

out_error:
    printf("  Probe failed with error\n");
    return err;
}

/*
 * FIXED version: Properly calls of_node_put(child) before early exit
 */
static int probe_fixed(struct device_node *np)
{
    struct device_node *child;
    void *childpdev;
    int err = 0;

    printf("\n--- FIXED probe() ---\n");

    for_each_available_child_of_node(np, child) {
        childpdev = of_platform_device_create(child, 1);
        if (!childpdev) {
            err = -1;
            printf("  [FIX] Calling of_node_put(child) before early exit\n");
            of_node_put(child);  /* FIX: Release reference before exit */
            goto out_error;
        }
    }

    printf("  Probe completed successfully\n");
    return 0;

out_error:
    printf("  Probe failed with error\n");
    return err;
}

/*
 * Create a simulated device tree for testing
 */
static struct device_node *create_test_tree(void)
{
    struct device_node *parent = calloc(1, sizeof(*parent));
    struct device_node *child1 = calloc(1, sizeof(*child1));
    struct device_node *child2 = calloc(1, sizeof(*child2));
    struct device_node *child3 = calloc(1, sizeof(*child3));
    struct device_node *child4 = calloc(1, sizeof(*child4));

    strcpy(parent->name, "ssi-controller");
    strcpy(child1->name, "ssi-port@0");
    strcpy(child2->name, "ssi-port@1");
    strcpy(child3->name, "ssi-port@2");
    strcpy(child4->name, "ssi-port@3");

    /* All children are available */
    child1->available = true;
    child2->available = true;
    child3->available = true;
    child4->available = true;

    /* Build tree structure */
    parent->child = child1;
    child1->sibling = child2;
    child2->sibling = child3;
    child3->sibling = child4;

    /* Initialize refcounts (simulating initial state) */
    atomic_init(&parent->refcount, 1);
    atomic_init(&child1->refcount, 1);
    atomic_init(&child2->refcount, 1);
    atomic_init(&child3->refcount, 1);
    atomic_init(&child4->refcount, 1);

    return parent;
}

/*
 * Check for refcount leaks
 */
static void check_refcount_leaks(struct device_node *parent)
{
    struct device_node *child = parent->child;
    int leaked_nodes = 0;

    printf("\n--- Refcount Status ---\n");
    while (child) {
        int ref = atomic_load(&child->refcount);
        printf("  %s: refcount = %d %s\n",
               child->name, ref,
               ref > 1 ? "[LEAKED!]" : "[OK]");
        if (ref > 1)
            leaked_nodes++;
        child = child->sibling;
    }

    printf("\n--- Summary ---\n");
    printf("  Total of_node_get() calls: %d\n", total_gets);
    printf("  Total of_node_put() calls: %d\n", total_puts);
    printf("  Leaked references: %d\n", total_gets - total_puts);
    printf("  Nodes with leaked refcount: %d\n", leaked_nodes);
}

/*
 * Free the test tree
 */
static void free_test_tree(struct device_node *parent)
{
    struct device_node *child = parent->child;
    while (child) {
        struct device_node *next = child->sibling;
        free(child);
        child = next;
    }
    free(parent);
}

int main(void)
{
    struct device_node *tree;

    printf("=== POC: Linux Kernel Refcount Leak Bug ===\n");
    printf("Commit: 9a2ea132df860177b33c9fd421b26c4e9a0a9396\n");
    printf("Bug: Missing of_node_put() on early exit from for_each_available_child_of_node\n");

    /* Test BUGGY version */
    printf("\n========== Testing BUGGY Version ==========\n");
    tree = create_test_tree();
    total_gets = 0;
    total_puts = 0;

    probe_buggy(tree);
    check_refcount_leaks(tree);

    if (total_gets != total_puts) {
        printf("\n[BUG CONFIRMED] Refcount leak detected!\n");
        printf("  The 'child' node reference was not released on early exit.\n");
    }

    free_test_tree(tree);

    /* Test FIXED version */
    printf("\n\n========== Testing FIXED Version ==========\n");
    tree = create_test_tree();
    total_gets = 0;
    total_puts = 0;

    probe_fixed(tree);
    check_refcount_leaks(tree);

    if (total_gets == total_puts) {
        printf("\n[FIX VERIFIED] No refcount leak in fixed version.\n");
        printf("  The 'child' node reference is properly released on early exit.\n");
    }

    free_test_tree(tree);

    /* Print bug pattern analysis */
    printf("\n\n=== Bug Pattern Analysis ===\n");
    printf("Bug Type: CWE-911 (Improper Update of Reference Count)\n\n");
    printf("Four-Features Pattern:\n");
    printf("  Target API: for_each_available_child_of_node() macro\n");
    printf("              (internally uses of_get_next_available_child())\n");
    printf("  Post-operation: of_node_put()\n");
    printf("  Critical variable: child (struct device_node*)\n");
    printf("  Path condition: Early exit via goto/break/return from loop\n\n");
    printf("Fix: Call of_node_put(child) before any early exit from the loop.\n");

    return 0;
}
