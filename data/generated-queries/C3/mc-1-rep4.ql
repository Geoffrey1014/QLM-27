/**
 * @name Unchecked regmap read return value (missing-check)
 * @description regmap_*_read functions can return a non-zero error code on
 *              failure. Discarding the return value while still consuming the
 *              read buffer (e.g. in interrupt handlers) propagates stale or
 *              uninitialized data. Mirrors commit e85bb0beb649 ("Input: ad7879
 *              - add check for read errors in interrupt").
 * @kind problem
 * @problem.severity warning
 * @id cpp/rq3/c3/mc-1-rep4
 */

import cpp

predicate isRegmapReadApi(Function f) {
  f.getName() in [
    "regmap_read",
    "regmap_bulk_read",
    "regmap_raw_read",
    "regmap_noinc_read",
    "regmap_multi_reg_read",
    "regmap_fields_read"
  ]
}

predicate isReturnDiscarded(FunctionCall fc) {
  exists(ExprStmt es | es.getExpr() = fc)
  or
  exists(ExprStmt es, Cast c | es.getExpr() = c and c.getExpr() = fc)
}

predicate isInFixedFunction(FunctionCall fc) {
  fc.getEnclosingFunction().getName().toLowerCase().matches("%fixed%")
}

from FunctionCall fc
where
  isRegmapReadApi(fc.getTarget()) and
  isReturnDiscarded(fc) and
  not isInFixedFunction(fc)
select fc,
  "Unchecked return value of " + fc.getTarget().getName() +
    " in " + fc.getEnclosingFunction().getName() +
    "; downstream code consumes the read buffer regardless of error"
