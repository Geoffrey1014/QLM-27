/**
 * @name Unnecessary GFP_ATOMIC in non-atomic context (delay-gfp)
 * @description Detects calls passing GFP_ATOMIC to allocator/submit APIs
 *              from a function whose body shows no evidence of running in
 *              atomic context (no spinlock held across the call, no IRQ
 *              handler entry point, no preempt_disable, no GFP_ATOMIC
 *              already required by caller context). Pattern source: DCNS
 *              (Bai et al.) — replace with GFP_KERNEL.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-dgfp-4
 */

import cpp

/** Allocator / submit functions whose last argument is a gfp_t flags. */
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

/** An expression that names GFP_ATOMIC (handles macro and identifier forms). */
predicate isGfpAtomic(Expr e) {
  exists(MacroInvocation mi | mi.getMacroName() = "GFP_ATOMIC" and mi.getExpr() = e)
  or
  e.toString() = "GFP_ATOMIC"
}

/** Names that hint the enclosing function may run in atomic context. */
predicate looksAtomicContextName(Function f) {
  exists(string n | n = f.getName() |
    n.matches("%_irq%") or
    n.matches("%irq_handler%") or
    n.matches("%_isr%") or
    n.matches("%_atomic%") or
    n.matches("%_tasklet%") or
    n.matches("%_softirq%") or
    n.matches("%timer_fn%")
  )
}

/** Function holds (or appears to hold) a spinlock around the body. */
predicate functionTakesSpinlock(Function f) {
  exists(FunctionCall fc | fc.getEnclosingFunction() = f |
    fc.getTarget().getName().matches("spin_lock%") or
    fc.getTarget().getName().matches("raw_spin_lock%") or
    fc.getTarget().getName().matches("read_lock%") or
    fc.getTarget().getName().matches("write_lock%") or
    fc.getTarget().getName() = "local_irq_disable" or
    fc.getTarget().getName() = "local_irq_save" or
    fc.getTarget().getName() = "preempt_disable" or
    fc.getTarget().getName() = "rcu_read_lock"
  )
}

/** Function has a gfp_t parameter — likely a helper that propagates flags. */
predicate functionTakesGfpParam(Function f) {
  exists(Parameter p | p = f.getAParameter() |
    p.getType().getName() = "gfp_t" or
    p.getType().toString() = "gfp_t"
  )
}

from FunctionCall call, Function callee, Function caller, Expr gfpArg, int idx
where
  callee = call.getTarget() and
  isGfpTakingFunction(callee) and
  // The gfp_t flag argument is the last formal parameter of callee.
  idx = callee.getNumberOfParameters() - 1 and
  gfpArg = call.getArgument(idx) and
  isGfpAtomic(gfpArg) and
  caller = call.getEnclosingFunction() and
  // Caller shows no sign of atomic context.
  not looksAtomicContextName(caller) and
  not functionTakesSpinlock(caller) and
  not functionTakesGfpParam(caller)
select call,
  "Call to " + callee.getName() +
  " uses GFP_ATOMIC inside non-atomic function " + caller.getName() +
  "; consider GFP_KERNEL."
