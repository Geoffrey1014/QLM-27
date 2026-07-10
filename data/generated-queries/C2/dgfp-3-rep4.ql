/**
 * @name  rq3-c2-dgfp-3-rep4
 * @id    cpp/rq3/c2/dgfp-3-rep4
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects GFP_ATOMIC passed to kernel allocators in functions that
 *              appear to run in sleepable context (init/probe-style), suggesting
 *              GFP_KERNEL could be used instead (delay-gfp pattern).
 */

import cpp

/** A macro invocation that expands the GFP_ATOMIC token. */
predicate isGfpAtomicMacro(MacroInvocation mi) {
  mi.getMacroName() = "GFP_ATOMIC"
}

/** A call to a kernel allocator that takes a gfp flag, where the gfp argument
 *  expands the GFP_ATOMIC macro. `gfpArg` is bound to the actual argument expression. */
predicate isAllocCallWithGfpAtomic(FunctionCall fc, Expr gfpArg) {
  exists(string name | name = fc.getTarget().getName() |
    name = "kmalloc" or
    name = "kzalloc" or
    name = "kcalloc" or
    name = "kmalloc_array" or
    name = "krealloc" or
    name = "kmalloc_node" or
    name = "kzalloc_node" or
    name = "kmem_cache_alloc" or
    name = "alloc_skb" or
    name = "__alloc_skb" or
    name = "vmalloc" or
    name = "vzalloc"
  ) and
  exists(MacroInvocation mi |
    isGfpAtomicMacro(mi) and
    gfpArg = fc.getAnArgument() and
    mi.getExpr() = gfpArg
  )
}

/** Heuristic: function looks like an init / probe / setup / open routine —
 *  i.e. very likely to run in sleepable (process / module-init) context. */
predicate isInitLikeFunction(Function f) {
  exists(string n | n = f.getName() |
    n.matches("%_init") or
    n.matches("%_init_%") or
    n.matches("init_%") or
    n.matches("%_probe") or
    n.matches("%_setup") or
    n.matches("%_open") or
    n.matches("%_create") or
    n.matches("%_register") or
    n.matches("%_alloc")
  )
}

/** Heuristic: function name suggests it MAY be invoked from atomic context
 *  (IRQ handlers, tasklets, timers, atomic helpers). When true we want to
 *  *exclude* the function from the report — GFP_ATOMIC may genuinely be needed. */
predicate mayBeCalledFromAtomic(Function f) {
  exists(string n | n = f.getName() |
    n.matches("%_irq") or
    n.matches("%_irq_%") or
    n.matches("%irq_handler%") or
    n.matches("%_isr") or
    n.matches("%_atomic") or
    n.matches("%_atomic_%") or
    n.matches("%_tasklet%") or
    n.matches("%_timer") or
    n.matches("%_callback") or
    n.matches("%_rcu") or
    n.matches("%_rcu_%")
  )
}

/** The enclosing function of `fc` is plausibly sleepable: it looks init-like
 *  AND does not look like an atomic-context callback. */
predicate enclosingFunctionIsSleepable(FunctionCall fc, Function enc) {
  enc = fc.getEnclosingFunction() and
  isInitLikeFunction(enc) and
  not mayBeCalledFromAtomic(enc)
}

from FunctionCall fc, Function enc, Expr gfp
where
  isAllocCallWithGfpAtomic(fc, gfp) and
  enclosingFunctionIsSleepable(fc, enc)
select fc,
  "GFP_ATOMIC used inside sleepable function $@; consider replacing with GFP_KERNEL.",
  enc, enc.getName()
