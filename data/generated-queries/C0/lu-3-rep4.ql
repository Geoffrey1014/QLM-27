/**
 * @name pm_runtime_get_sync without put on error path
 * @description pm_runtime_get_sync() increments the usage counter even when it
 *              fails. If the caller returns early on the error branch without
 *              calling pm_runtime_put() / pm_runtime_put_noidle(), the runtime
 *              PM reference count leaks.
 * @kind problem
 * @problem.severity warning
 * @id cpp/pm-runtime-get-sync-leak
 * @tags correctness
 *       reliability
 *       resource-leak
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph

/**
 * A call to a pm_runtime_get_sync-family function whose return value is
 * checked for an error (<0) and on that error path the function returns
 * without performing a balancing pm_runtime_put*.
 */

class PmRuntimeGetSyncCall extends FunctionCall {
  PmRuntimeGetSyncCall() {
    this.getTarget().getName() = "pm_runtime_get_sync" or
    this.getTarget().getName() = "pm_runtime_resume_and_get" or
    this.getTarget().getName() = "__pm_runtime_resume"
  }
}

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
 * Holds if `bb` (or any block reachable from it staying within `f` and not
 * passing through a pm_runtime_put*) contains a ReturnStmt.
 *
 * We approximate: there exists a return-stmt reachable from `getSync` whose
 * path does not include any PmRuntimePutCall.
 */
predicate errorReturnWithoutPut(PmRuntimeGetSyncCall getSync, ReturnStmt ret) {
  exists(Function f, IfStmt ifs |
    getSync.getEnclosingFunction() = f and
    ret.getEnclosingFunction() = f and
    // the if-condition syntactically references the return value of getSync,
    // via comparison with a negative literal (`ret < 0`) or similar.
    ifs.getEnclosingFunction() = f and
    exists(Variable v, AssignExpr a |
      a.getRValue() = getSync and
      a.getLValue() = v.getAnAccess() and
      ifs.getCondition().getAChild*() = v.getAnAccess()
    )
    and
    // return is inside (or is) the then-branch of that if
    (ret.getParent*() = ifs.getThen() or ret = ifs.getThen())
    and
    // no pm_runtime_put* between the getSync call and the return inside the
    // same function
    not exists(PmRuntimePutCall put |
      put.getEnclosingFunction() = f and
      put.getLocation().getStartLine() >= getSync.getLocation().getStartLine() and
      put.getLocation().getStartLine() <= ret.getLocation().getStartLine()
    )
  )
}

from PmRuntimeGetSyncCall getSync, ReturnStmt ret
where
  errorReturnWithoutPut(getSync, ret) and
  // exclude void-returning helpers that wouldn't propagate the error anyway
  exists(getSync.getEnclosingFunction())
select getSync,
  "pm_runtime_get_sync() return value is checked but the error path at $@ " +
    "returns without calling pm_runtime_put*, leaking a runtime-PM reference.",
  ret, "this return"
