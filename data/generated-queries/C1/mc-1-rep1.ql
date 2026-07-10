/**
 * @name Missing check of error-returning call
 * @description A call to a function that returns an integer error code is
 *              issued as a bare expression statement: the return value is
 *              discarded with neither assignment nor immediate test. Such
 *              missing-check sites can mask I/O / hardware failures.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-mc-1
 */

import cpp

/** Heuristic: a function whose name suggests it performs a fallible
 *  I/O / hardware / register / lookup style operation and returns an
 *  int error code (0 == OK, non-zero == error). */
bindingset[n]
predicate isErrorReturningName(string n) {
  n.matches("%_read%") or
  n.matches("%_write%") or
  n.matches("%regmap%") or
  n.matches("%_bulk_%") or
  n.matches("%_transfer%") or
  n.matches("%_xfer%") or
  n.matches("%_send%") or
  n.matches("%_recv%") or
  n.matches("%_probe%") or
  n.matches("%_setup%") or
  n.matches("%_get_%") or
  n.matches("%_set_%") or
  n.matches("%_request%") or
  n.matches("%_enable%") or
  n.matches("%_disable%")
}

from FunctionCall fc, Function callee, ExprStmt es
where
  fc.getTarget() = callee and
  isErrorReturningName(callee.getName()) and
  // Return type is an integer (typical kernel error-code style).
  callee.getType() instanceof IntType and
  // The call is the entire expression of a statement, i.e. value dropped.
  es.getExpr() = fc
select fc,
  "Return value of '" + callee.getName() +
    "()' is discarded; this function returns an int error code that " +
    "should be checked before proceeding."
