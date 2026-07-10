/**
 * @name C3 generated query for mc-1 / fix e85bb0beb649
 * @description Missing return-value check on regmap_bulk_read() — CWE-252 missing error check
 * @kind problem
 * @problem.severity warning
 * @id cpp/rq3/c3/mc-1-rep3
 */

import cpp

predicate isErrorReturningRead(FunctionCall fc) {
  fc.getTarget().getName() in [
    "regmap_bulk_read",
    "regmap_read",
    "regmap_noinc_read",
    "regmap_raw_read",
    "regmap_multi_reg_read"
  ]
}

predicate returnValueIgnored(FunctionCall fc) {
  // The FunctionCall expression is used as a statement on its own —
  // i.e. its immediate parent is an ExprStmt, so the int return value
  // is dropped on the floor with no assignment, comparison, or use.
  exists(ExprStmt es | es.getExpr() = fc)
}

predicate isInFixedFunction(FunctionCall fc) {
  fc.getEnclosingFunction().getName().toLowerCase().matches("%fixed%")
}

from FunctionCall readCall
where
  isErrorReturningRead(readCall) and
  returnValueIgnored(readCall) and
  not isInFixedFunction(readCall)
select readCall,
  "Call to " + readCall.getTarget().getName() +
    " ignores its int return value; on failure subsequent code uses the" +
    " partially/uninitialised buffer (CWE-252 missing error check)"
