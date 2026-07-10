/**
 * @name Missing pm_runtime_put on pm_runtime_get_sync failure
 * @description pm_runtime_get_sync() (and siblings) increment the device's
 *              runtime PM usage counter even when they return a negative
 *              error. Failing to call pm_runtime_put() in the error path
 *              leaks a reference and prevents the device from ever
 *              suspending.
 * @kind problem
 * @problem.severity warning
 * @id cpp/pm-runtime-get-sync-refcount-leak
 * @tags reliability
 *       correctness
 *       resource-leak
 */

import cpp

/**
 * A call to a member of the pm_runtime_get* family that bumps the
 * runtime-PM usage counter and requires a paired pm_runtime_put*() even
 * when the call returns a negative error code.
 */
class PmRuntimeGetSyncCall extends FunctionCall {
  PmRuntimeGetSyncCall() {
    exists(string n | n = this.getTarget().getName() |
      n = "pm_runtime_get_sync" or
      n = "pm_runtime_resume_and_get" or
      n = "__pm_runtime_resume"
    )
  }
}

/** A call that releases one reference taken by pm_runtime_get*. */
class PmRuntimePutCall extends FunctionCall {
  PmRuntimePutCall() {
    exists(string n | n = this.getTarget().getName() |
      n = "pm_runtime_put" or
      n = "pm_runtime_put_sync" or
      n = "pm_runtime_put_noidle" or
      n = "pm_runtime_put_autosuspend" or
      n = "pm_runtime_put_sync_autosuspend" or
      n = "pm_runtime_put_sync_suspend" or
      n = "__pm_runtime_put"
    )
  }
}

/**
 * Holds if `ifs` is an if-statement that tests the result of `get` on the
 * error path and immediately follows `get`.
 *   ret = pm_runtime_get_sync(dev);
 *   if (ret < 0)            // or  if (ret)
 *           return ret;
 */
predicate errorCheckOfGet(IfStmt ifs, PmRuntimeGetSyncCall get, Variable retVar) {
  exists(ExprStmt assignStmt, AssignExpr ae |
    assignStmt.getExpr() = ae and
    ae.getRValue() = get and
    ae.getLValue() = retVar.getAnAccess()
  ) and
  exists(Expr cond | cond = ifs.getCondition() |
    cond = retVar.getAnAccess()
    or
    cond.(LTExpr).getLeftOperand() = retVar.getAnAccess()
    or
    cond.(NEExpr).getAnOperand() = retVar.getAnAccess()
    or
    cond.(NotExpr).getOperand().(GEExpr).getLeftOperand() = retVar.getAnAccess()
  ) and
  ifs.getEnclosingFunction() = get.getEnclosingFunction() and
  ifs.getLocation().getStartLine() > get.getLocation().getStartLine() and
  ifs.getLocation().getStartLine() < get.getLocation().getStartLine() + 6
}

/**
 * Holds if the then-branch of `ifs` exits the function (return/goto)
 * without first calling pm_runtime_put* on the same device argument as
 * `get`.
 */
predicate thenBranchLeaksRef(IfStmt ifs, PmRuntimeGetSyncCall get) {
  exists(Stmt thenBranch | thenBranch = ifs.getThen() |
    exists(Stmt exitStmt |
      exitStmt.getParentStmt*() = thenBranch and
      (exitStmt instanceof ReturnStmt or exitStmt instanceof GotoStmt)
    ) and
    not exists(PmRuntimePutCall put, VariableAccess putArg, VariableAccess getArg |
      put.getEnclosingStmt().getParentStmt*() = thenBranch and
      putArg = put.getArgument(0) and
      getArg = get.getArgument(0) and
      putArg.getTarget() = getArg.getTarget()
    )
  )
}

from PmRuntimeGetSyncCall get, IfStmt ifs, Variable retVar
where
  errorCheckOfGet(ifs, get, retVar) and
  thenBranchLeaksRef(ifs, get) and
  get.getArgument(0) instanceof VariableAccess
select get,
  "pm_runtime_get_sync() may leak a runtime-PM reference: the error branch at $@ returns without calling pm_runtime_put().",
  ifs, "this check"
