/**
 * @name Missing check of regmap_bulk_read return value
 * @description regmap_bulk_read (and similar fallible accessors) returns a
 *              negative error code on failure. Ignoring the return value
 *              and using the destination buffer can propagate stale/invalid
 *              data. This query flags call sites where the return value
 *              of such a function is discarded (the call is a statement
 *              expression with no use of its result).
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-mc-1
 * @tags correctness
 *       reliability
 */

import cpp

/**
 * Heuristic: a function whose return type is `int` (or any integer) AND
 * which, by its name, plausibly performs a fallible I/O / read / get /
 * fetch / probe / lookup / query / acquire operation. This is the generic
 * pattern the patch fixes — the specific instance here is
 * `regmap_bulk_read`, but we must generalise to find the same class of
 * defect elsewhere in the kernel.
 */
predicate isFallibleAccessor(Function f) {
  f.getType().getUnspecifiedType() instanceof IntegralType and
  exists(string n | n = f.getName().toLowerCase() |
    n.matches("%_read%") or
    n.matches("%_write%") or
    n.matches("%_get%") or
    n.matches("%_set%") or
    n.matches("%_send%") or
    n.matches("%_recv%") or
    n.matches("%_fetch%") or
    n.matches("%_probe%") or
    n.matches("%_query%") or
    n.matches("%_request%") or
    n.matches("%_xfer%") or
    n.matches("%_transfer%") or
    n.matches("%_update%") or
    n.matches("%_sync%") or
    n.matches("%_poll%") or
    n.matches("%regmap_%") or
    n.matches("%i2c_%") or
    n.matches("%spi_%")
  )
}

/**
 * A call is "result-discarded" when its enclosing expression context is
 * an ExprStmt — i.e., the call appears as a statement on its own, with
 * no surrounding assignment, comparison, return, condition, or argument
 * use.
 */
predicate resultDiscarded(FunctionCall fc) {
  exists(ExprStmt s | s.getExpr() = fc)
}

from FunctionCall fc, Function callee, Function caller
where
  callee = fc.getTarget() and
  isFallibleAccessor(callee) and
  resultDiscarded(fc) and
  caller = fc.getEnclosingFunction()
select fc,
  "Return value of fallible accessor '" + callee.getName() +
  "' is discarded in '" + caller.getName() +
  "'; failures (negative error codes) will be silently ignored."
