/**
 * @name  rq3-c2-mc-1-rep5
 * @id    cpp/rq3/c2/mc-1-rep5
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Missing-check pattern: calls to error-returning APIs whose
 *              return value is discarded.
 */

import cpp

predicate is_target_api_call(FunctionCall fc) {
  exists(string n | n = fc.getTarget().getName() |
    n = "regmap_bulk_read" or
    n = "regmap_read" or
    n = "regmap_raw_read" or
    n = "regmap_noinc_read"
  )
  and fc.getTarget().getType().getUnspecifiedType() instanceof IntType
}

predicate return_value_ignored(FunctionCall fc) {
  exists(ExprStmt es | es.getExpr() = fc)
}

predicate in_irq_or_callback(FunctionCall fc) {
  exists(Function f | f = fc.getEnclosingFunction() |
    f.getType().getName().toLowerCase().matches("%irqreturn%") or
    f.getName().toLowerCase().matches("%_irq%") or
    f.getName().toLowerCase().matches("%_handler%") or
    f.getName().toLowerCase().matches("%_callback%")
  )
}

predicate no_error_check_after(FunctionCall fc) {
  is_target_api_call(fc) and
  return_value_ignored(fc)
}

predicate missing_check_bug(FunctionCall fc) {
  is_target_api_call(fc) and
  no_error_check_after(fc)
}

from FunctionCall fc
where missing_check_bug(fc)
select fc, "Call to error-returning API '" + fc.getTarget().getName() +
  "' whose return value is not checked (missing-check bug pattern)."
