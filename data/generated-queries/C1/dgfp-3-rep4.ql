/**
 * @name Delayable GFP_ATOMIC allocation in a sleepable context (dgfp-3 rep4)
 * @description Reports calls to kernel allocation helpers that pass
 *              GFP_ATOMIC from a function whose call-graph context is
 *              plausibly sleepable (not under spin_lock, not an IRQ
 *              handler, not an atomic-only callback). These are
 *              candidates for the delay-gfp pattern: GFP_ATOMIC can be
 *              relaxed to GFP_KERNEL.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-dgfp-3
 * @tags correctness
 *       performance
 *       memory
 */

import cpp

/* Allocation APIs whose gfp flag argument is meaningful. */
predicate allocApiGfpArg(string name, int argIdx) {
  name = "kmalloc" and argIdx = 1 or
  name = "kzalloc" and argIdx = 1 or
  name = "kcalloc" and argIdx = 2 or
  name = "kmalloc_array" and argIdx = 2 or
  name = "krealloc" and argIdx = 2 or
  name = "kmemdup" and argIdx = 2 or
  name = "kstrdup" and argIdx = 1 or
  name = "kstrndup" and argIdx = 2 or
  name = "kmem_cache_alloc" and argIdx = 1 or
  name = "kmem_cache_zalloc" and argIdx = 1 or
  name = "kmem_cache_alloc_node" and argIdx = 2 or
  name = "alloc_skb" and argIdx = 1 or
  name = "__alloc_skb" and argIdx = 1 or
  name = "alloc_pages" and argIdx = 0 or
  name = "__get_free_pages" and argIdx = 0 or
  name = "get_zeroed_page" and argIdx = 0 or
  name = "alloc_workqueue" and argIdx = 1 or
  name = "kvmalloc" and argIdx = 1 or
  name = "kvzalloc" and argIdx = 1
}

/* Recognise an expression denoting GFP_ATOMIC, whether macro-expanded
 * or surviving as the literal token. */
predicate isGfpAtomicExpr(Expr e) {
  exists(MacroInvocation mi |
    mi.getMacro().getName() = "GFP_ATOMIC" and
    mi.getExpr() = e
  )
  or
  e.toString().regexpMatch(".*GFP_ATOMIC.*")
  or
  e.getValue().toInt() = 32
}

/* A function looks "sleepable" by name: init/probe/setup/open/create/
 * register/configure/start path. */
predicate sleepableContext(Function f) {
  f.getName().regexpMatch("(?i).*(init|probe|setup|open|create|alloc|register|configure|start).*")
  or
  exists(FunctionCall fc, Expr arg, string callee, int idx |
    fc.getEnclosingFunction() = f and
    callee = fc.getTarget().getName() and
    allocApiGfpArg(callee, idx) and
    arg = fc.getArgument(idx) and
    arg.toString().regexpMatch(".*GFP_KERNEL.*")
  )
}

/* Suppression: function looks atomic / takes a spinlock. */
predicate inAtomicContext(Function f) {
  f.getName().regexpMatch("(?i).*(irq_handler|isr|_irq$|_atomic$|tasklet|softirq|timer_fn).*")
  or
  exists(FunctionCall fc, string n |
    fc.getEnclosingFunction() = f and
    n = fc.getTarget().getName() and
    n.regexpMatch("(?i)(spin_lock(_irq(save)?)?|raw_spin_lock(_irq(save)?)?|local_irq_save|local_irq_disable|preempt_disable|rcu_read_lock)")
  )
}

from FunctionCall call, Function caller, string apiName, int gfpIdx, Expr gfpArg
where
  caller = call.getEnclosingFunction() and
  apiName = call.getTarget().getName() and
  allocApiGfpArg(apiName, gfpIdx) and
  gfpArg = call.getArgument(gfpIdx) and
  isGfpAtomicExpr(gfpArg) and
  sleepableContext(caller) and
  not inAtomicContext(caller)
select call,
  "Potential delay-gfp: " + apiName + "(..., GFP_ATOMIC) inside '" +
    caller.getName() + "' which appears to be a sleepable context; " +
    "consider GFP_KERNEL."
