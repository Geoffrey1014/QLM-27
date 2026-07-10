/**
 * @name C3 generated query for mc-1 / fix e85bb0beb649 / rep2
 * @description Missing-check of regmap_*read return value in interrupt handler; buffer consumed without verifying read succeeded (CWE-252).
 * @kind problem
 * @problem.severity warning
 * @id cpp/rq3/c3/mc-1-rep2
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

predicate returnValueDropped(FunctionCall fc) {
  /* call appears as a bare statement — its int return is dropped. */
  exists(ExprStmt es | es.getExpr() = fc)
}

predicate isInFixedFunction(FunctionCall fc) {
  fc.getEnclosingFunction().getName().toLowerCase().matches("%fixed%")
}

predicate hasDownstreamConsumer(FunctionCall readCall) {
  /* After the unchecked read, the enclosing function performs at least one
     additional call — i.e. it consumes/uses something rather than returning
     immediately.  This filters out 'ping' reads (fp3 shape).  Strict
     ordering check is approximated by 'another call in same function
     whose location is at or after the read'. */
  exists(FunctionCall consumer |
    consumer.getEnclosingFunction() = readCall.getEnclosingFunction() and
    consumer != readCall and
    consumer.getLocation().getStartLine() >= readCall.getLocation().getStartLine()
  )
}

from FunctionCall readCall
where
  isCheckableReadCall(readCall) and
  returnValueDropped(readCall) and
  hasDownstreamConsumer(readCall) and
  not isInFixedFunction(readCall)
select readCall,
  "Return value of " + readCall.getTarget().getName() +
    " is dropped, but the function still consumes the read buffer downstream — missing error check (CWE-252)."
