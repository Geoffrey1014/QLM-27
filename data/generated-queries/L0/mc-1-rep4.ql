/**
 * @name Missing check of regmap_bulk_read return value
 * @description Return value of a checkable regmap read API is dropped as
 *              an expression statement; the caller cannot know whether the
 *              buffer it filled is valid before consuming it (CWE-252).
 * @kind problem
 * @problem.severity warning
 * @id cpp/missing-check-regmap-read
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

from FunctionCall readCall, ExprStmt es
where
  isCheckableReadCall(readCall) and
  es.getExpr() = readCall and
  not readCall.getEnclosingFunction().getName().toLowerCase().matches("%fixed%")
select readCall,
  "Return value of " + readCall.getTarget().getName() + " is dropped (missing error check, CWE-252)."
