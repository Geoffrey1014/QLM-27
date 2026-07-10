/**
 * @name  rq3-c2-dgfp-3-rep3
 * @id    cpp/rq3/c2/dgfp-3-rep3
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects kzalloc/kmalloc calls using GFP_ATOMIC inside functions
 *              that are never reachable from any atomic context (no spinlock,
 *              no IRQ handler, no preempt-disabled region, no RCU read lock).
 */

import cpp

/** Holds if the expression `e` is the GFP flag `GFP_ATOMIC` (possibly via a macro). */
predicate is_gfp_atomic_arg(Expr e) {
  e.toString() = "GFP_ATOMIC"
  or
  exists(MacroInvocation mi |
    mi.getMacroName() = "GFP_ATOMIC" and
    mi.getExpr() = e
  )
}

/** Holds if `fc` is an allocation call (k*alloc family) whose gfp flags argument is GFP_ATOMIC. */
predicate is_alloc_with_gfp_atomic(FunctionCall fc) {
  exists(string name | name = fc.getTarget().getName() |
    name = "kmalloc" or
    name = "kzalloc" or
    name = "kcalloc" or
    name = "kmalloc_array" or
    name = "kvmalloc" or
    name = "kvzalloc" or
    name = "kmemdup" or
    name = "krealloc"
  ) and
  exists(Expr gfp | gfp = fc.getAnArgument() | is_gfp_atomic_arg(gfp))
}

/** Holds if `fc` is a call that acquires an atomic context (spinlock, irq disable, preempt disable, rcu read lock). */
predicate is_atomic_acquire_call(FunctionCall fc) {
  exists(string n | n = fc.getTarget().getName() |
    n = "spin_lock" or
    n = "spin_lock_bh" or
    n = "spin_lock_irq" or
    n = "spin_lock_irqsave" or
    n = "_raw_spin_lock" or
    n = "_raw_spin_lock_irq" or
    n = "_raw_spin_lock_irqsave" or
    n = "_raw_spin_lock_bh" or
    n = "read_lock" or
    n = "read_lock_irq" or
    n = "read_lock_irqsave" or
    n = "read_lock_bh" or
    n = "write_lock" or
    n = "write_lock_irq" or
    n = "write_lock_irqsave" or
    n = "write_lock_bh" or
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
 * Holds if function `f` may itself execute in atomic context — either it
 * directly takes an atomic-acquiring call, or its name pattern marks it as
 * an IRQ/atomic handler.
 */
predicate function_may_be_atomic(Function f) {
  exists(FunctionCall fc | fc.getEnclosingFunction() = f and is_atomic_acquire_call(fc))
  or
  // Heuristic: handlers / callbacks that run in IRQ / softirq / tasklet / timer context.
  f.getName().matches("%_irq_handler")
  or
  f.getName().matches("%_isr")
  or
  f.getName().matches("%_tasklet")
  or
  f.getName().matches("%_timer_fn")
  or
  f.getName().matches("%_softirq")
}

/** Holds if function `f` is *never* in atomic context — neither itself nor any of its callers. */
predicate function_never_atomic(Function f) {
  not function_may_be_atomic(f) and
  not exists(Function caller, FunctionCall call |
    call.getEnclosingFunction() = caller and
    call.getTarget() = f and
    function_may_be_atomic(caller)
  )
}

from FunctionCall fc, Function enc
where
  is_alloc_with_gfp_atomic(fc) and
  enc = fc.getEnclosingFunction() and
  function_never_atomic(enc)
select fc,
  "Allocation uses GFP_ATOMIC inside function '" + enc.getName() +
    "' which is never called from atomic context; GFP_KERNEL would suffice."
