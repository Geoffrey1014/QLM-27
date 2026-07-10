/**
 * @name  rq3-c2-dgfp-3-rep1
 * @id    cpp/rq3/c2/dgfp-3-rep1
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *   Detects unnecessary use of GFP_ATOMIC in allocator calls whose
 *   enclosing function is not reachable from an atomic context.
 */

import cpp

predicate is_alloc_call(FunctionCall fc) {
  fc.getTarget().getName() in [
    "kmalloc", "kzalloc", "kcalloc", "krealloc",
    "kmalloc_array", "kmem_cache_alloc", "kmem_cache_zalloc",
    "vmalloc", "vzalloc", "__get_free_pages", "alloc_pages",
    "kmalloc_node", "kzalloc_node"
  ]
}

predicate uses_gfp_atomic(FunctionCall fc) {
  is_alloc_call(fc) and
  exists(Expr arg | arg = fc.getAnArgument() |
    arg.toString().matches("%GFP_ATOMIC%") or
    exists(MacroInvocation mi |
      mi.getMacroName() = "GFP_ATOMIC" and
      mi.getExpr() = arg
    )
  )
}

predicate is_atomic_context_fn(Function f) {
  exists(string n | n = f.getName() |
    n.matches("%_irq") or
    n.matches("%_irqsave") or
    n.matches("%_atomic") or
    n.matches("%_locked") or
    n.matches("%_handler") or
    n.matches("%_isr") or
    n.matches("%_tasklet") or
    n.matches("%_timer") or
    n.matches("%_softirq")
  )
  or
  exists(FunctionCall lc |
    lc.getEnclosingFunction() = f and
    lc.getTarget().getName().matches("spin_lock%")
  )
  or
  exists(FunctionCall lc |
    lc.getEnclosingFunction() = f and
    lc.getTarget().getName().matches("rcu_read_lock%")
  )
}

predicate may_run_in_atomic(Function f) {
  is_atomic_context_fn(f)
  or
  exists(Function caller, FunctionCall fc |
    may_run_in_atomic(caller) and
    fc.getEnclosingFunction() = caller and
    fc.getTarget() = f
  )
}

predicate unnecessary_gfp_atomic(FunctionCall fc, Function enclosing) {
  uses_gfp_atomic(fc) and
  enclosing = fc.getEnclosingFunction() and
  not may_run_in_atomic(enclosing)
}

from FunctionCall fc, Function f
where unnecessary_gfp_atomic(fc, f)
select fc, "Unnecessary GFP_ATOMIC in " + f.getName() + " which is never reached from atomic context."
