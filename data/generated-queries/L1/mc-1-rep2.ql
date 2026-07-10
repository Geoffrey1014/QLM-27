/**
 * @name Missing check for regmap_bulk_read return value
 * @description regmap_bulk_read (and analogous read APIs) returns int; the
 *              return value must be checked. This query flags call sites where
 *              the returned status is discarded (call issued as an
 *              expression-statement).
 * @kind problem
 * @problem.severity warning
 * @id qlm/l1/mc-1-rep2
 */

import cpp

predicate isCheckedReadApiCall(FunctionCall fc) {
  fc.getTarget().getName() = "regmap_bulk_read"
}

predicate returnValueDiscarded(FunctionCall fc) {
  exists(ExprStmt es | es.getExpr() = fc)
}

from FunctionCall fc
where isCheckedReadApiCall(fc) and returnValueDiscarded(fc)
select fc, "return value of " + fc.getTarget().getName() + " is discarded (missing error check)"
