/**
 * @name Unchecked regmap read return value
 * @description The regmap_*_read family of functions can return a non-zero
 *              error code on failure. Ignoring the return value and using the
 *              data buffer regardless can lead to acting on stale or
 *              uninitialized data (e.g. in interrupt handlers).
 * @kind problem
 * @problem.severity warning
 * @id cpp/unchecked-regmap-read
 * @tags reliability
 *       correctness
 */

import cpp
import semmle.code.cpp.controlflow.Guards

/**
 * Functions in the regmap read family whose int return value indicates
 * success (0) or an error code (non-zero). Missing this check can cause
 * the caller to operate on garbage data.
 */
predicate isRegmapReadFunction(Function f) {
  exists(string n | n = f.getName() |
    n = "regmap_read" or
    n = "regmap_bulk_read" or
    n = "regmap_raw_read" or
    n = "regmap_noinc_read" or
    n = "regmap_multi_reg_read" or
    n = "regmap_fields_read" or
    n = "regmap_read_poll_timeout" or
    n = "regmap_bulk_read_async"
  )
}

/**
 * An ExprStmt whose expression is a direct call to a regmap read function,
 * i.e. the return value is discarded entirely.
 */
predicate isDiscardedRegmapRead(FunctionCall fc) {
  isRegmapReadFunction(fc.getTarget()) and
  exists(ExprStmt es | es.getExpr() = fc)
}

/**
 * Holds if the result of `fc` is consumed by any expression that could
 * represent an error-check (comparison, assignment to a variable later
 * tested, passed to IS_ERR-like macro, etc.).
 *
 * For the discarded case we already know the call is a stand-alone
 * statement, so we only fire on `isDiscardedRegmapRead`.
 */
predicate resultUsed(FunctionCall fc) {
  exists(Element parent | parent = fc.getParent() and not parent instanceof ExprStmt)
}

from FunctionCall fc, Function caller
where
  isRegmapReadFunction(fc.getTarget()) and
  caller = fc.getEnclosingFunction() and
  isDiscardedRegmapRead(fc) and
  not resultUsed(fc)
select fc,
  "Return value of " + fc.getTarget().getName() +
    "() is ignored; this function can fail and leave the output buffer with stale/undefined data."
