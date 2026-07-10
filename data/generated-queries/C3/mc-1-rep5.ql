/**
 * @name C3 generated query for mc-1 / fix e85bb0beb649
 * @description Missing check of regmap_*_read return value — buffer consumed unconditionally (CWE-252)
 * @kind problem
 * @problem.severity warning
 * @id cpp/rq3/c3/mc-1-rep5
 */

import cpp

predicate isRegmapReadCall(FunctionCall fc) {
  fc.getTarget().getName() in [
    "regmap_read",
    "regmap_bulk_read",
    "regmap_raw_read",
    "regmap_noinc_read",
    "regmap_fields_read",
    "regmap_multi_reg_read"
  ]
}

predicate isReturnValueDiscarded(FunctionCall fc) {
  exists(ExprStmt es | es.getExpr() = fc)
}

predicate isReturnValueCaptured(FunctionCall fc) {
  exists(AssignExpr a | a.getRValue() = fc)
  or
  exists(Variable v | v.getInitializer().getExpr() = fc)
}

predicate isReturnValueChecked(FunctionCall fc) {
  exists(Element parent | parent = fc.getParent() and not parent instanceof ExprStmt)
}

predicate isInFixedFunction(FunctionCall fc) {
  fc.getEnclosingFunction().getName().toLowerCase().matches("%fixed%")
}

from FunctionCall fc
where
  isRegmapReadCall(fc) and
  isReturnValueDiscarded(fc) and
  not isReturnValueCaptured(fc) and
  not isReturnValueChecked(fc) and
  not isInFixedFunction(fc)
select fc,
  "Return value of " + fc.getTarget().getName() +
    "() is ignored; this function can fail and leave the output buffer with stale/undefined data."
