/**
 * @name GFP_ATOMIC used in sleepable (non-atomic) context
 * @description Detects calls that pass a GFP_ATOMIC flag to a kernel allocation
 *              / URB submission API from a function that does not appear to run
 *              in atomic context (IRQ handler, spinlock-held helper, RCU
 *              read-side critical section, etc.).  When the caller is in
 *              process (sleepable) context, GFP_KERNEL should be used so the
 *              allocator may sleep and so the system is not put under undue
 *              memory pressure.  This is the delay-gfp / DCNS pattern
 *              (Bai et al., 2018).
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-dgfp-4
 * @tags correctness
 *       performance
 *       kernel
 */

import cpp

/* Kernel APIs that accept a gfp_t flag as one of their arguments and
 * for which GFP_KERNEL is the right default in sleepable context.
 * Includes URB submission, memory allocators, and a handful of common
 * GFP-flag-consuming helpers. */
predicate gfpTakingApi(string name, int gfpArgIndex) {
  name = "usb_submit_urb"      and gfpArgIndex = 1 or
  name = "kmalloc"             and gfpArgIndex = 1 or
  name = "kzalloc"             and gfpArgIndex = 1 or
  name = "kcalloc"             and gfpArgIndex = 2 or
  name = "krealloc"            and gfpArgIndex = 2 or
  name = "vmalloc"             and gfpArgIndex = 1 or
  name = "kmem_cache_alloc"    and gfpArgIndex = 1 or
  name = "alloc_skb"           and gfpArgIndex = 1 or
  name = "__alloc_skb"         and gfpArgIndex = 1 or
  name = "alloc_pages"         and gfpArgIndex = 0 or
  name = "__get_free_pages"    and gfpArgIndex = 0 or
  name = "dma_alloc_coherent"  and gfpArgIndex = 3 or
  name = "dma_pool_alloc"      and gfpArgIndex = 1 or
  name = "mempool_alloc"       and gfpArgIndex = 1
}

/* An expression that refers to the GFP_ATOMIC flag (either the bare
 * macro name, or an OR-combination containing it).  GFP_ATOMIC is a
 * preprocessor macro, so by the time the AST sees it the token is a
 * numeric literal; we therefore match on (a) any sub-expression whose
 * source text exactly is "GFP_ATOMIC", recoverable from the AST via
 * `Expr.toString()` only for variable references — for literals we
 * fall back to the EnumConstantAccess / VariableAccess names that the
 * extractor preserves. */
predicate isGfpAtomic(Expr e) {
  e.(VariableAccess).getTarget().getName() = "GFP_ATOMIC"
  or
  e.(EnumConstantAccess).getTarget().getName() = "GFP_ATOMIC"
  or
  exists(MacroInvocation mi |
    mi.getMacroName() = "GFP_ATOMIC" and
    mi.getExpr() = e
  )
  or
  /* OR-combination of flags that includes GFP_ATOMIC. */
  exists(BinaryOperation bo | bo = e and bo.getOperator() = "|" |
    isGfpAtomic(bo.getLeftOperand()) or isGfpAtomic(bo.getRightOperand())
  )
}

/* Conservative name-based heuristic for atomic / interrupt / lock-held
 * context.  When the caller's name unambiguously signals such a
 * context, GFP_ATOMIC is appropriate and we don't flag. */
predicate atomicContextFunction(Function f) {
  exists(string n | n = f.getName().toLowerCase() |
    n.matches("%_isr") or
    n.matches("%_irq") or
    n.matches("%_irq_%") or
    n.matches("%irq_handler%") or
    n.matches("%_handler") or
    n.matches("%_interrupt") or
    n.matches("%_nmi%") or
    n.matches("%_atomic%") or
    n.matches("%_tasklet%") or
    n.matches("%_softirq%") or
    n.matches("%_complete") or
    n.matches("%_callback") or
    n.matches("%_cb") or
    n.matches("%_timer%") or
    n.matches("%poll%") or
    n.matches("%_rx") or
    n.matches("%_tx")
  )
}

/* A function whose name suggests it runs in process (sleepable)
 * context: probe/remove/init/exit/open/release/ioctl/read/write/
 * suspend/resume/work/thread, etc. */
predicate sleepableContextFunction(Function f) {
  exists(string n, string tok |
    n = f.getName() and
    tok = ["init", "exit", "probe", "remove", "open", "release", "close",
           "suspend", "resume", "ioctl", "read", "write", "show", "store",
           "thread", "work", "worker", "workfn", "reset", "setup", "start",
           "stop", "attach", "detach", "xfer", "transfer", "register",
           "unregister", "create", "destroy", "load", "unload"] |
    n.matches("%_" + tok) or
    n.matches("%_" + tok + "_%") or
    n = tok
  )
}

from FunctionCall fc, Function callee, Function caller, int gfpIdx, Expr gfpArg
where
  callee = fc.getTarget() and
  gfpTakingApi(callee.getName(), gfpIdx) and
  gfpArg = fc.getArgument(gfpIdx) and
  isGfpAtomic(gfpArg) and
  caller = fc.getEnclosingFunction() and
  sleepableContextFunction(caller) and
  not atomicContextFunction(caller)
select fc,
  "Call to " + callee.getName() + "() passes GFP_ATOMIC from sleepable function '"
    + caller.getName() + "'; consider GFP_KERNEL."
