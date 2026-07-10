/**
 * @name Unnecessary GFP_ATOMIC in non-atomic init context
 * @description Allocation functions (kmalloc/kzalloc/kcalloc/kmem_cache_alloc/
 *              vmalloc family) are called with GFP_ATOMIC inside functions
 *              that are only reached from non-atomic (process / init) context.
 *              GFP_ATOMIC trades off allocation success for latency; using it
 *              where sleeping is allowed wastes the emergency reserves and is
 *              a known Linux-kernel anti-pattern (see e.g. commit
 *              a0732548ba03 "net: tipc: bcast: Replace GFP_ATOMIC with
 *              GFP_KERNEL in tipc_bcast_init()").
 * @kind problem
 * @problem.severity warning
 * @id cpp/linux-unnecessary-gfp-atomic
 * @tags reliability
 *       performance
 *       linux-kernel
 */

import cpp

/**
 * Allocation-family functions that take a `gfp_t` flag argument.
 * The flag-argument position varies per API.
 */
predicate allocApi(string name, int flagArg) {
  name = "kmalloc" and flagArg = 1
  or
  name = "kzalloc" and flagArg = 1
  or
  name = "kcalloc" and flagArg = 2
  or
  name = "kmalloc_array" and flagArg = 2
  or
  name = "kzalloc_node" and flagArg = 1
  or
  name = "kmalloc_node" and flagArg = 1
  or
  name = "kmem_cache_alloc" and flagArg = 1
  or
  name = "kmem_cache_zalloc" and flagArg = 1
  or
  name = "kstrdup" and flagArg = 1
  or
  name = "kstrndup" and flagArg = 2
  or
  name = "kmemdup" and flagArg = 2
  or
  name = "vmalloc" and flagArg = -1 // no flag, ignore
  or
  name = "alloc_skb" and flagArg = 1
  or
  name = "__alloc_skb" and flagArg = 1
  or
  name = "netdev_alloc_skb" and flagArg = 1
  or
  name = "sock_kmalloc" and flagArg = 2
  or
  name = "krealloc" and flagArg = 2
}

/** A call to an allocation function with GFP_ATOMIC as its gfp flag. */
class GfpAtomicAllocCall extends FunctionCall {
  GfpAtomicAllocCall() {
    exists(string name, int flagArg |
      allocApi(name, flagArg) and
      flagArg >= 0 and
      this.getTarget().getName() = name and
      this.getArgument(flagArg).toString().regexpMatch(".*GFP_ATOMIC.*")
    )
  }
}

/**
 * Functions that are heuristically known to run in non-atomic (sleepable)
 * context. We use naming conventions widely followed in the kernel:
 *   - `*_init`, `*_probe`, `*_open`, `*_setup`, `*_create`, `*_register`,
 *     `*_attach`, `*_mount`, `*_show`, `*_store` (sysfs handlers run in
 *     process context), `*_ioctl`.
 *
 * This is intentionally conservative: matching the original commit
 * (tipc_bcast_init) and other similar non-atomic init paths.
 */
predicate nonAtomicByName(Function f) {
  exists(string n | n = f.getName() |
    n.regexpMatch(".*_init") or
    n.regexpMatch(".*_probe") or
    n.regexpMatch(".*_open") or
    n.regexpMatch(".*_setup") or
    n.regexpMatch(".*_create") or
    n.regexpMatch(".*_register") or
    n.regexpMatch(".*_attach") or
    n.regexpMatch(".*_mount") or
    n.regexpMatch(".*_show") or
    n.regexpMatch(".*_store") or
    n.regexpMatch(".*_ioctl") or
    n.regexpMatch("init_.*") or
    n.regexpMatch("probe_.*")
  )
}

/**
 * Heuristic: the enclosing function (or one of its callers up to depth 2)
 * is a known sleepable context.
 */
predicate inNonAtomicContext(Function f) {
  nonAtomicByName(f)
  or
  exists(Function caller, FunctionCall c |
    c.getTarget() = f and
    c.getEnclosingFunction() = caller and
    nonAtomicByName(caller)
  )
}

/**
 * Filter out cases where the enclosing function itself is plausibly atomic:
 * IRQ handlers, timer callbacks, tasklets, atomic-named helpers.
 */
predicate plausiblyAtomicByName(Function f) {
  exists(string n | n = f.getName() |
    n.regexpMatch(".*_isr") or
    n.regexpMatch(".*_irq") or
    n.regexpMatch(".*_irq_handler") or
    n.regexpMatch(".*interrupt.*") or
    n.regexpMatch(".*tasklet.*") or
    n.regexpMatch(".*_timer") or
    n.regexpMatch(".*_callback") or
    n.regexpMatch(".*atomic.*") or
    n.regexpMatch(".*_rcu")
  )
}

from GfpAtomicAllocCall call, Function enclosing
where
  enclosing = call.getEnclosingFunction() and
  inNonAtomicContext(enclosing) and
  not plausiblyAtomicByName(enclosing)
select call,
  "Allocation with GFP_ATOMIC in function '" + enclosing.getName() +
    "' which appears to run in non-atomic (sleepable) context; GFP_KERNEL is likely sufficient."
