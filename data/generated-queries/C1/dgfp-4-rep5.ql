/**
 * @name Unnecessary GFP_ATOMIC in non-atomic context
 * @description An allocation flag of GFP_ATOMIC is passed inside a function
 *              whose name does not suggest it ever runs in atomic context
 *              (IRQ handler, NMI handler, tasklet, spinlock-holding helper,
 *              etc.). Such calls waste the emergency atomic memory pool;
 *              GFP_KERNEL is preferable.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-dgfp-4
 */

import cpp

/**
 * Heuristic: does the enclosing function name suggest it may execute in
 * atomic context (where GFP_ATOMIC is required)?
 */
predicate isLikelyAtomicContext(Function f) {
  exists(string n | n = f.getName().toLowerCase() |
    n.matches("%_isr") or
    n.matches("%isr_%") or
    n.matches("%_irq%") or
    n.matches("%irq_%") or
    n.matches("%_handler") or
    n.matches("%_nmi%") or
    n.matches("%_interrupt%") or
    n.matches("%spin_%") or
    n.matches("%_atomic%") or
    n.matches("%_tasklet%") or
    n.matches("%_bh") or
    n.matches("%_softirq%") or
    n.matches("%_callback") or
    n.matches("%_complete") or
    n.matches("%_completion")
  )
}

/**
 * Holds if `e` is an expression that evaluates (transitively through
 * references / casts / parenthesisation) to the GFP_ATOMIC flag.
 * We accept either the macro use (`Expr.findRootCause` -> Macro) or the
 * literal integer value (0x20 / 32) emitted after macro expansion.
 */
predicate isGfpAtomicExpr(Expr e) {
  // The expression text in source mentions GFP_ATOMIC (catches the
  // GFP_ATOMIC macro use directly).
  exists(MacroInvocation mi |
    mi.getMacroName() = "GFP_ATOMIC" and
    mi.getExpr() = e
  )
  or
  // Fallback: a compile-time constant whose value matches GFP_ATOMIC (0x20).
  // This catches POC stubs that #define GFP_ATOMIC to the canonical value
  // when kernel headers are not present.
  e.getValue().toInt() = 32 and
  e.getType().getUnspecifiedType() instanceof IntegralType and
  not exists(MacroInvocation mi2 |
    mi2.getMacroName() = "GFP_KERNEL" and mi2.getExpr() = e
  )
}

from FunctionCall fc, Function enclosing, int argIdx, Expr flagArg
where
  enclosing = fc.getEnclosingFunction() and
  flagArg = fc.getArgument(argIdx) and
  isGfpAtomicExpr(flagArg) and
  not isLikelyAtomicContext(enclosing)
select fc,
  "GFP_ATOMIC passed to '" + fc.getTarget().getName() +
  "' (argument " + argIdx.toString() +
  ") inside non-atomic-looking function '" + enclosing.getName() +
  "'; consider GFP_KERNEL instead."
