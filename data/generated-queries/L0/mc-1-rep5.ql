/**
 * @name Missing return-value check on regmap read then consume buffer
 * @description Detects calls to regmap_*read whose int return is dropped while
 *              the enclosing function still consumes the read buffer via a
 *              subsequent call — CWE-252 (Unchecked Return Value).
 * @kind problem
 * @problem.severity warning
 * @id cpp/qlllm/mc-1-rep5-L0
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

from FunctionCall readCall, ExprStmt es, FunctionCall consumer
where
  isCheckableReadCall(readCall) and
  es.getExpr() = readCall and
  consumer.getEnclosingFunction() = readCall.getEnclosingFunction() and
  consumer != readCall and
  consumer.getLocation().getStartLine() >= readCall.getLocation().getStartLine() and
  not readCall.getEnclosingFunction().getName().toLowerCase().matches("%fixed%")
select readCall,
  "Return value of " + readCall.getTarget().getName() +
    " is dropped, but the function still consumes the read buffer downstream — missing error check (CWE-252)."
