/**
 * @name pm_runtime_get_sync without matching put on error path
 * @description When pm_runtime_get_sync (or a similar refcount-bumping
 *              acquire API) returns a negative value, the runtime PM
 *              counter has still been incremented. Failure to call
 *              pm_runtime_put on the error path causes a reference
 *              count leak. This query detects functions that check
 *              `ret < 0` after such an acquire and return without
 *              calling the matching release.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-lu-3
 */

import cpp

/* Acquire APIs that bump a refcount even on failure. */
predicate isRefcountAcquire(string name) {
  name = "pm_runtime_get_sync" or
  name = "pm_runtime_get" or
  name = "pm_runtime_get_noresume" or
  name = "pm_runtime_resume_and_get"
}

/* Matching release APIs that decrement the refcount. */
predicate isRefcountRelease(string name) {
  name = "pm_runtime_put" or
  name = "pm_runtime_put_sync" or
  name = "pm_runtime_put_autosuspend" or
  name = "pm_runtime_put_noidle" or
  name = "__pm_runtime_put_autosuspend"
}

/* An IfStmt that checks "x < 0" (the acquire return value). */
predicate isNegativeCheck(IfStmt ifs, Variable v) {
  exists(RelationalOperation rel |
    rel = ifs.getCondition().getAChild*() and
    rel.getOperator() = "<" and
    rel.getLeftOperand().(VariableAccess).getTarget() = v and
    rel.getRightOperand().getValue() = "0"
  )
}

/* True if the given Stmt contains (recursively) a release call. */
predicate stmtContainsRelease(Stmt s) {
  exists(FunctionCall release, ExprStmt es |
    isRefcountRelease(release.getTarget().getName()) and
    release.getEnclosingStmt() = es and
    es.getParent*() = s
  )
  or
  exists(FunctionCall release |
    isRefcountRelease(release.getTarget().getName()) and
    release.getEnclosingStmt() = s
  )
}

/* True if the given Stmt contains (recursively) a return. */
predicate stmtContainsReturn(Stmt s) {
  exists(ReturnStmt rs | rs.getParent*() = s)
}

/* The then-branch of the if returns without going through any release call. */
predicate returnsWithoutRelease(IfStmt ifs) {
  stmtContainsReturn(ifs.getThen()) and
  not stmtContainsRelease(ifs.getThen())
}

from FunctionCall acquireCall, Variable retVar, AssignExpr assign, IfStmt errCheck, Function f
where
  acquireCall.getEnclosingFunction() = f and
  isRefcountAcquire(acquireCall.getTarget().getName()) and
  assign.getRValue() = acquireCall and
  assign.getLValue() = retVar.getAnAccess() and
  errCheck.getEnclosingFunction() = f and
  isNegativeCheck(errCheck, retVar) and
  // The if comes after the acquire (same function, lexically later).
  errCheck.getLocation().getStartLine() > acquireCall.getLocation().getStartLine() and
  returnsWithoutRelease(errCheck)
select errCheck,
  "Reference count leak: " + acquireCall.getTarget().getName() +
  " was called but no matching release on the error path in " + f.getName() + "."
