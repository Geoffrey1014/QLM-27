/**
 * @name Delayable GFP_ATOMIC allocation in a sleepable context
 * @description Reports calls to allocation helpers (kzalloc / kmalloc /
 *              kcalloc / krealloc / kmem_cache_alloc / vmalloc family /
 *              alloc_skb / etc.) that pass the GFP_ATOMIC flag from a
 *              function whose call-graph context is plausibly sleepable
 *              (i.e. not an IRQ/atomic helper, not under spin_lock, not
 *              from an atomic-only callback). Such calls are candidates
 *              for the "delay-gfp" pattern: GFP_ATOMIC can be relaxed to
 *              GFP_KERNEL.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-dgfp-3
 * @tags correctness
 *       performance
 *       memory
 */

import cpp

/* Allocation APIs whose gfp flag argument is meaningful. The position
 * of the gfp flag varies, so we encode (function name, arg index). */
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
  name = "kvzalloc" and argIdx = 1 or
  name = "vmalloc" and argIdx = 0  // vmalloc has no gfp arg; placeholder
}

/* Recognise an expression that ultimately denotes GFP_ATOMIC. We accept
 * the macro-expanded constant 0x20 (typical Linux value), the literal
 * identifier text, and reference exprs whose name matches. */
predicate isGfpAtomicExpr(Expr e) {
  // Macro-expanded form: any expr whose generating macro is GFP_ATOMIC.
  exists(MacroInvocation mi |
    mi.getMacro().getName() = "GFP_ATOMIC" and
    mi.getExpr() = e
  )
  or
  // Source text mentions GFP_ATOMIC literally.
  e.toString().regexpMatch(".*GFP_ATOMIC.*")
  or
  // Bare integer constant that equals the canonical GFP_ATOMIC value
  // and appears in a context where the macro might have been already
  // expanded by the preprocessor (e.g. mini-DB extraction).
  e.getValue().toInt() = 32
}

/* A function looks "sleepable" if its name suggests init / setup / probe
 * / open path, OR it directly calls something that may sleep. We keep
 * this lightweight (name-based) since the C1 cell is monolithic. */
predicate sleepableContext(Function f) {
  f.getName().regexpMatch("(?i).*(init|probe|setup|open|create|alloc|register|configure|start).*")
  or
  // Calls a function that itself takes GFP_KERNEL somewhere – evidence
  // the surrounding context can sleep.
  exists(FunctionCall fc, Expr arg, string callee, int idx |
    fc.getEnclosingFunction() = f and
    callee = fc.getTarget().getName() and
    allocApiGfpArg(callee, idx) and
    arg = fc.getArgument(idx) and
    arg.toString().regexpMatch(".*GFP_KERNEL.*")
  )
}

/* Suppression: the function (or any function it transitively calls in a
 * shallow 1-hop way) takes a spinlock / disables IRQs / is an IRQ
 * handler. We approximate by name. */
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
