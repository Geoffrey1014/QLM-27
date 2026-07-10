/**
 * @name Unnecessary GFP_ATOMIC allocation in non-atomic context
 * @description Detects calls passing GFP_ATOMIC to allocator/submit APIs
 *              inside functions that are never invoked from an atomic context
 *              and that do not themselves hold a spinlock, disable preemption,
 *              or run in an IRQ handler. In such cases GFP_KERNEL should be
 *              used instead (pattern from em28xx_init_usb_xfer fix:
 *              "Replace GFP_ATOMIC with GFP_KERNEL").
 * @kind problem
 * @problem.severity warning
 * @id cpp/unnecessary-gfp-atomic
 * @tags efficiency
 *       correctness
 */

import cpp

/**
 * Functions whose last argument is a gfp_t flags parameter and therefore
 * may legitimately take either GFP_ATOMIC or GFP_KERNEL. We focus on the
 * common Linux allocator / submit families.
 */
predicate isGfpTakingFunction(Function f) {
  exists(string n | n = f.getName() |
    n = "usb_submit_urb" or
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
    n = "dev_alloc_skb" or
    n = "__netdev_alloc_skb" or
    n = "netdev_alloc_skb" or
    n = "alloc_pages" or
    n = "__get_free_pages" or
    n = "get_zeroed_page" or
    n = "dma_alloc_coherent" or
    n = "dma_pool_alloc" or
    n = "mempool_alloc"
  )
}

/** An expression that evaluates to GFP_ATOMIC. */
predicate isGfpAtomic(Expr e) {
  exists(MacroInvocation mi |
    mi.getMacroName() = "GFP_ATOMIC" and
    mi.getExpr() = e
  )
  or
  // Fallback: literal-ish reference to GFP_ATOMIC identifier
  exists(string s | s = e.toString() | s = "GFP_ATOMIC")
}

/**
 * Heuristic: a function is potentially called from atomic context if its
 * body itself acquires a spinlock, disables interrupts/preemption, holds
 * an RCU read lock, OR if its name suggests an IRQ / atomic / callback
 * entry point (irq handler, tasklet, timer callback, completion handler,
 * notifier).
 */
predicate looksAtomic(Function f) {
  exists(FunctionCall fc | fc.getEnclosingFunction() = f |
    exists(string n | n = fc.getTarget().getName() |
      n.matches("spin_lock%") or
      n.matches("raw_spin_lock%") or
      n.matches("_raw_spin_lock%") or
      n.matches("read_lock%") or
      n.matches("write_lock%") or
      n = "local_irq_disable" or
      n = "local_irq_save" or
      n = "preempt_disable" or
      n = "rcu_read_lock" or
      n = "rcu_read_lock_bh" or
      n = "rcu_read_lock_sched"
    )
  )
  or
  exists(string fn | fn = f.getName() |
    fn.matches("%_irq") or
    fn.matches("%_isr") or
    fn.matches("%_interrupt") or
    fn.matches("%_irq_handler") or
    fn.matches("%_tasklet%") or
    fn.matches("%_timer%") or
    fn.matches("%_callback") or
    fn.matches("%_complete") or
    fn.matches("%_completion") or
    fn.matches("%_notify") or
    fn.matches("%_notifier")
  )
}

/**
 * A function reachable (transitively, up to a small depth) from an
 * atomic-looking caller. We approximate with a direct-caller check plus
 * one indirection — full transitive closure tends to be too noisy.
 */
predicate calledFromAtomic(Function f) {
  exists(FunctionCall fc |
    fc.getTarget() = f and
    looksAtomic(fc.getEnclosingFunction())
  )
  or
  exists(FunctionCall fc, Function mid |
    fc.getTarget() = f and
    fc.getEnclosingFunction() = mid and
    exists(FunctionCall fc2 |
      fc2.getTarget() = mid and
      looksAtomic(fc2.getEnclosingFunction())
    )
  )
}

from FunctionCall call, Function callee, Function caller, Expr gfpArg
where
  callee = call.getTarget() and
  isGfpTakingFunction(callee) and
  caller = call.getEnclosingFunction() and
  // GFP flag is the last argument
  gfpArg = call.getArgument(call.getNumberOfArguments() - 1) and
  isGfpAtomic(gfpArg) and
  // Caller is not itself atomic-looking
  not looksAtomic(caller) and
  // Caller is not (heuristically) called from atomic context
  not calledFromAtomic(caller)
select call,
  "GFP_ATOMIC passed to $@ inside non-atomic function '" + caller.getName() +
    "'; consider GFP_KERNEL.", callee, callee.getName()
