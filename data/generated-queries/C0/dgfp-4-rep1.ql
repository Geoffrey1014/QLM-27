/**
 * @name Unnecessary GFP_ATOMIC allocation in non-atomic context
 * @description Detects calls that pass GFP_ATOMIC as an allocation flag from a
 *              function that is never invoked in atomic context (no callers hold
 *              spinlocks, run in IRQ handlers, or disable preemption).
 *              Such calls should use GFP_KERNEL instead to avoid wasting the
 *              atomic memory reserve.
 * @kind problem
 * @problem.severity warning
 * @id cpp/delay-gfp-atomic-in-sleepable
 * @tags correctness
 *       performance
 */

import cpp

/**
 * A macro invocation expanding to the GFP_ATOMIC flag.
 */
class GfpAtomicMacro extends MacroInvocation {
  GfpAtomicMacro() { this.getMacroName() = "GFP_ATOMIC" }
}

/**
 * Functions known to require a `gfp_t` flag argument. We restrict to the most
 * common kernel allocators / submitters so we look at meaningful call sites.
 */
predicate isAllocatorLike(Function f) {
  exists(string n | n = f.getName() |
    n = "kmalloc" or
    n = "kzalloc" or
    n = "kcalloc" or
    n = "krealloc" or
    n = "kmalloc_array" or
    n = "kmem_cache_alloc" or
    n = "kmem_cache_zalloc" or
    n = "vmalloc" or
    n = "vzalloc" or
    n = "alloc_skb" or
    n = "__alloc_skb" or
    n = "dev_alloc_skb" or
    n = "netdev_alloc_skb" or
    n = "usb_alloc_urb" or
    n = "usb_submit_urb" or
    n = "usb_alloc_coherent" or
    n = "dma_alloc_coherent" or
    n = "kasprintf" or
    n = "kvasprintf" or
    n = "kstrdup" or
    n = "kmemdup" or
    n = "kzalloc_node" or
    n = "kmalloc_node"
  )
}

/**
 * Functions whose presence on the call stack indicates atomic context.
 * Used as a conservative proxy: if `f` (or anything `f` calls transitively)
 * acquires one of these, treat the body after the acquire as atomic.
 */
predicate isAtomicEntryFunction(Function f) {
  exists(string n | n = f.getName() |
    n = "spin_lock" or
    n = "spin_lock_bh" or
    n = "spin_lock_irq" or
    n = "spin_lock_irqsave" or
    n = "_raw_spin_lock" or
    n = "_raw_spin_lock_bh" or
    n = "_raw_spin_lock_irq" or
    n = "_raw_spin_lock_irqsave" or
    n = "read_lock" or
    n = "read_lock_bh" or
    n = "read_lock_irq" or
    n = "read_lock_irqsave" or
    n = "write_lock" or
    n = "write_lock_bh" or
    n = "write_lock_irq" or
    n = "write_lock_irqsave" or
    n = "rcu_read_lock" or
    n = "rcu_read_lock_bh" or
    n = "rcu_read_lock_sched" or
    n = "preempt_disable" or
    n = "local_irq_disable" or
    n = "local_irq_save" or
    n = "local_bh_disable"
  )
}

/**
 * A function that may run in atomic context: either it is itself an IRQ-like
 * handler entry, or it directly invokes something that establishes atomic
 * context (spin_lock family, rcu_read_lock, preempt_disable, etc.).
 */
predicate mayRunInAtomic(Function f) {
  // Direct atomic-establishing call inside the function body.
  exists(FunctionCall fc | fc.getEnclosingFunction() = f and isAtomicEntryFunction(fc.getTarget()))
  or
  // Heuristic name-based: handler / callback / isr functions are commonly atomic.
  exists(string n | n = f.getName() |
    n.matches("%_isr") or
    n.matches("%_irq_handler") or
    n.matches("%_interrupt") or
    n.matches("%_callback")
  )
}

/**
 * A function reachable (directly or transitively) only from non-atomic call
 * sites. Conservative under-approximation: if no caller in the database may
 * run in atomic context AND the function itself does not establish atomic
 * context, then GFP_ATOMIC is unnecessary inside it.
 */
predicate isSleepableFunction(Function f) {
  not mayRunInAtomic(f) and
  not exists(FunctionCall caller |
    caller.getTarget() = f and
    mayRunInAtomic(caller.getEnclosingFunction())
  )
}

from FunctionCall call, GfpAtomicMacro gfp, Function enclosing, Function callee
where
  enclosing = call.getEnclosingFunction() and
  callee = call.getTarget() and
  isAllocatorLike(callee) and
  // GFP_ATOMIC token appears among the call arguments.
  exists(Expr arg |
    arg = call.getAnArgument() and
    gfp.getExpr() = arg
  ) and
  isSleepableFunction(enclosing)
select call,
  "Call to $@ uses GFP_ATOMIC in $@, which appears never to run in atomic context; consider GFP_KERNEL.",
  callee, callee.getName(), enclosing, enclosing.getName()
