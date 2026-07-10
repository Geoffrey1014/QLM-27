/**
 * @name Missing pm_runtime_put on pm_runtime_get_sync failure (lu-3)
 * @description pm_runtime_get_sync() increments the runtime-PM usage
 *   counter even when it returns a negative error code. If the caller
 *   returns on that error path without invoking pm_runtime_put() (or
 *   pm_runtime_put_noidle()), the reference count is leaked.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-lu-3
 * @tags reliability correctness
 */

import cpp

/* A call to pm_runtime_get_sync (or its close variants that also bump
 * the usage counter on failure). */
predicate isGetSync(FunctionCall fc) {
  fc.getTarget().getName() = "pm_runtime_get_sync" or
  fc.getTarget().getName() = "pm_runtime_resume_and_get"
}

/* Any decrement-style runtime-PM API that releases the reference that
 * pm_runtime_get_sync acquired. */
predicate isPmPut(FunctionCall fc) {
  exists(string n | n = fc.getTarget().getName() |
    n = "pm_runtime_put" or
    n = "pm_runtime_put_sync" or
    n = "pm_runtime_put_noidle" or
    n = "pm_runtime_put_autosuspend" or
    n = "pm_runtime_put_sync_autosuspend" or
    n = "pm_runtime_put_sync_suspend" or
    n = "__pm_runtime_put_autosuspend"
  )
}

/* The "ret" assignment from pm_runtime_get_sync: capture the variable
 * that stores the return value. */
predicate getSyncRetVar(FunctionCall fc, Variable v) {
  exists(AssignExpr a |
    a.getRValue() = fc and
    a.getLValue() = v.getAnAccess()
  )
}

/* An IfStmt whose condition tests that ret is negative (e.g. ret < 0,
 * ret != 0, unlikely(ret), IS_ERR(ret) is not relevant here). */
predicate testsNegative(IfStmt ifs, Variable v) {
  exists(RelationalOperation rel |
    rel = ifs.getCondition().getAChild*() and
    rel.getAnOperand() = v.getAnAccess() and
    rel.getOperator() = "<"
  )
}

/* A then-branch whose only effect on the leaked reference is to return
 * without calling any pm_runtime_put variant. */
predicate thenBranchLeaksOnReturn(IfStmt ifs) {
  exists(ReturnStmt rs |
    rs.getEnclosingStmt*() = ifs.getThen() or
    rs = ifs.getThen() or
    rs.getParent*() = ifs.getThen()
  ) and
  not exists(FunctionCall put |
    isPmPut(put) and
    (put.getEnclosingStmt().getParent*() = ifs.getThen() or
     put.getEnclosingStmt() = ifs.getThen())
  )
}

from FunctionCall get, Variable ret, IfStmt ifs, Function f
where
  isGetSync(get) and
  getSyncRetVar(get, ret) and
  f = get.getEnclosingFunction() and
  ifs.getEnclosingFunction() = f and
  testsNegative(ifs, ret) and
  // the if-statement must come after the get_sync call
  ifs.getLocation().getStartLine() >= get.getLocation().getStartLine() and
  thenBranchLeaksOnReturn(ifs)
select get,
  "pm_runtime_get_sync() leaks a runtime-PM reference: the negative-return path at $@ exits without calling pm_runtime_put().",
  ifs, "this error branch"
