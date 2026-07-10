/**
 * @name rq3-c2-dgfp-4-rep1
 * @id cpp/rq3/c2/dgfp-4-rep1
 * @kind problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects calls passing GFP_ATOMIC where the enclosing function
 *              is not reachable from atomic context (delay-gfp / DCNS pattern).
 */
import cpp

/**
 * Holds if `e` is the expansion of the `GFP_ATOMIC` macro.
 */
predicate is_gfp_atomic(Expr e) {
  exists(MacroInvocation mi |
    mi.getMacroName() = "GFP_ATOMIC" and
    mi.getExpr() = e
  )
}

/**
 * Holds if function `f` takes a parameter at index `i` whose type is `gfp_t`.
 */
predicate has_gfp_param(Function f, int i) {
  exists(Parameter p |
    p = f.getParameter(i) and
    p.getType().getUnspecifiedType().getName() = "gfp_t"
  )
}

/**
 * Holds if call `c` passes `GFP_ATOMIC` as a gfp_t-typed argument to callee `callee`.
 */
predicate call_passes_atomic_flag(FunctionCall c, Function callee, int argIdx) {
  c.getTarget() = callee and
  has_gfp_param(callee, argIdx) and
  is_gfp_atomic(c.getArgument(argIdx))
}

/**
 * Holds if function `f`'s name suggests it runs in atomic context
 * (interrupt handler, tasklet, callback, atomic helper, etc).
 */
predicate name_suggests_atomic(Function f) {
  exists(string n | n = f.getName().toLowerCase() |
    n.matches("%isr%") or
    n.matches("%irq%") or
    n.matches("%interrupt%") or
    n.matches("%_atomic%") or
    n.matches("atomic_%") or
    n.matches("%tasklet%") or
    n.matches("%_cb") or
    n.matches("%_callback%") or
    n.matches("%complete%") or
    n.matches("%timer%")
  )
}

/**
 * Holds if function `f` is plausibly callable only from non-atomic (process) context:
 * its own name doesn't suggest atomic use, and no caller's name does either.
 * Conservative: requires the function to have at least one caller OR to be a static
 * helper whose name looks like a normal init/probe/open path.
 */
predicate enclosing_func_likely_non_atomic(Function f) {
  not name_suggests_atomic(f) and
  not exists(Function caller |
    caller.calls(f) and
    name_suggests_atomic(caller)
  ) and
  (
    f.getName().matches("%init%") or
    f.getName().matches("%probe%") or
    f.getName().matches("%open%") or
    f.getName().matches("%start%") or
    f.getName().matches("%setup%") or
    f.getName().matches("%register%") or
    f.getName().matches("%xfer%") or
    f.getName().matches("%submit%")
  )
}

/**
 * Holds if `c` is a call that passes `GFP_ATOMIC` from a function that is
 * likely not in atomic context — i.e. a candidate delay-gfp bug.
 */
predicate unnecessary_atomic_alloc(FunctionCall c) {
  exists(Function callee, int i, Function enclosing |
    call_passes_atomic_flag(c, callee, i) and
    enclosing = c.getEnclosingFunction() and
    enclosing_func_likely_non_atomic(enclosing)
  )
}

from FunctionCall c, Function enclosing
where
  unnecessary_atomic_alloc(c) and
  enclosing = c.getEnclosingFunction()
select c,
  "Call passes GFP_ATOMIC in function $@ which is likely not in atomic context; consider GFP_KERNEL.",
  enclosing, enclosing.getName()
