/**
 * @name Unnecessary GFP_ATOMIC allocation in non-atomic context
 * @description Detects allocation calls (kmalloc, kzalloc, kcalloc, etc.) that pass
 *              GFP_ATOMIC even though the enclosing function is never invoked from an
 *              atomic context (no spinlock held, no IRQ handler, no atomic caller).
 *              Such allocations should use GFP_KERNEL to allow the allocator to sleep
 *              and reclaim memory, improving robustness under memory pressure.
 * @kind problem
 * @problem.severity warning
 * @id cpp/unnecessary-gfp-atomic
 * @tags efficiency
 *       reliability
 */

import cpp

/**
 * Allocation-family functions in the kernel that take a gfp_t flags argument.
 * The flags argument position varies per function.
 */
predicate kernelAllocator(string name, int flagArgIndex) {
  name = "kmalloc" and flagArgIndex = 1
  or
  name = "kzalloc" and flagArgIndex = 1
  or
  name = "kmalloc_node" and flagArgIndex = 1
  or
  name = "kzalloc_node" and flagArgIndex = 1
  or
  name = "kcalloc" and flagArgIndex = 2
  or
  name = "kcalloc_node" and flagArgIndex = 2
  or
  name = "kmalloc_array" and flagArgIndex = 2
  or
  name = "kmalloc_array_node" and flagArgIndex = 2
  or
  name = "krealloc" and flagArgIndex = 2
  or
  name = "kvmalloc" and flagArgIndex = 1
  or
  name = "kvzalloc" and flagArgIndex = 1
  or
  name = "kvmalloc_node" and flagArgIndex = 1
  or
  name = "kvcalloc" and flagArgIndex = 2
  or
  name = "__get_free_pages" and flagArgIndex = 0
  or
  name = "alloc_pages" and flagArgIndex = 0
  or
  name = "alloc_pages_node" and flagArgIndex = 1
  or
  name = "__alloc_pages" and flagArgIndex = 0
  or
  name = "kmem_cache_alloc" and flagArgIndex = 1
  or
  name = "kmem_cache_zalloc" and flagArgIndex = 1
  or
  name = "mempool_alloc" and flagArgIndex = 1
}

/** Functions whose names indicate they are lock-acquiring (so callers of them are atomic). */
predicate lockAcquireFunction(Function f) {
  exists(string n | n = f.getName() |
    n.matches("spin_lock%") or
    n.matches("raw_spin_lock%") or
    n.matches("read_lock%") or
    n.matches("write_lock%") or
    n = "local_irq_disable" or
    n = "local_irq_save" or
    n = "local_bh_disable" or
    n = "preempt_disable" or
    n.matches("rcu_read_lock%")
  )
}

/** Heuristic: function name suggests it is invoked from atomic/IRQ context. */
predicate likelyAtomicContextFunction(Function f) {
  exists(string n | n = f.getName() |
    n.matches("%_irq") or
    n.matches("%_isr") or
    n.matches("%_interrupt") or
    n.matches("%_handler") or
    n.matches("%_callback") or
    n.matches("%_tasklet") or
    n.matches("%_timer") or
    n.matches("%_softirq") or
    n.matches("%_napi%") or
    n.matches("%_rx") or
    n.matches("%_tx")
  )
}

/** A function transitively reachable from an atomic-context caller. */
predicate calledFromAtomicContext(Function f) {
  likelyAtomicContextFunction(f)
  or
  exists(FunctionCall fc, Function caller |
    caller = fc.getEnclosingFunction() and
    fc.getTarget() = f and
    calledFromAtomicContext(caller)
  )
  or
  // function is called while a spinlock is held in some caller
  exists(FunctionCall fc, FunctionCall lockCall, Function caller |
    caller = fc.getEnclosingFunction() and
    fc.getTarget() = f and
    lockCall.getEnclosingFunction() = caller and
    lockAcquireFunction(lockCall.getTarget()) and
    lockCall.getLocation().getStartLine() < fc.getLocation().getStartLine()
  )
}

/** A GFP_ATOMIC expression: macro use or the literal name. */
predicate isGfpAtomic(Expr e) {
  exists(MacroInvocation mi |
    mi.getMacroName() = "GFP_ATOMIC" and
    mi.getExpr() = e
  )
  or
  e.toString().regexpMatch(".*GFP_ATOMIC.*")
}

from FunctionCall call, Function callee, int idx, Expr flagArg, Function enclosing
where
  callee = call.getTarget() and
  kernelAllocator(callee.getName(), idx) and
  idx >= 0 and
  flagArg = call.getArgument(idx) and
  isGfpAtomic(flagArg) and
  enclosing = call.getEnclosingFunction() and
  // The enclosing function is *not* called from an atomic context
  not calledFromAtomicContext(enclosing) and
  // Exclude functions that themselves take/hold a lock around the call
  not exists(FunctionCall lockCall |
    lockCall.getEnclosingFunction() = enclosing and
    lockAcquireFunction(lockCall.getTarget()) and
    lockCall.getLocation().getStartLine() < call.getLocation().getStartLine()
  ) and
  // Exclude functions whose names suggest atomic role
  not likelyAtomicContextFunction(enclosing)
select call,
  "Unnecessary GFP_ATOMIC in '" + callee.getName() +
    "' called from '" + enclosing.getName() +
    "', which is not invoked in atomic context. Consider GFP_KERNEL."
