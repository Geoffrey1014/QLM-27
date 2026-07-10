/**
 * @name Missing return-value check on regmap read (dropped return)
 * @description Detects calls to regmap_*read whose int return is used as a
 *              bare expression statement (return value dropped), meaning the
 *              caller cannot know whether the read succeeded — CWE-252
 *              (Unchecked Return Value). Composed of two predicates:
 *              isCheckableReadCall (target-API set) and isDroppedReturn
 *              (expression-statement discard).
 * @kind problem
 * @problem.severity warning
 * @id cpp/qlllm/mc-1-rep5-l1
 */

import cpp

predicate isCheckableReadCall(FunctionCall fc) {
  fc.getTarget().getName() in [
    "regmap_bulk_read",
    "regmap_read",
    "regmap_noinc_read",
    "regmap_raw_read"
  ]
}

predicate isDroppedReturn(FunctionCall fc) {
  exists(ExprStmt es | es.getExpr() = fc)
}

from FunctionCall readCall
where
  isCheckableReadCall(readCall) and
  isDroppedReturn(readCall) and
  not readCall.getEnclosingFunction().getName().toLowerCase().matches("%fixed%")
select readCall,
  "Return value of " + readCall.getTarget().getName() +
    " is dropped (used as bare expression statement) — missing error check (CWE-252)."
