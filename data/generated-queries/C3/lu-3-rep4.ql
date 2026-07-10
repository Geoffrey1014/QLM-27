/**
 * @name pm_runtime_get_sync refcount leak on error return path
 * @description pm_runtime_get_sync increments the runtime-PM usage counter
 *              even when it returns a negative error code. An error-handling
 *              path that simply returns the error without calling
 *              pm_runtime_put leaks the counter. Detects call sites whose
 *              early-error return path lacks a balancing pm_runtime_put.
 * @kind problem
 * @problem.severity warning
 * @id qlm/pm-runtime-get-sync-refcount-leak
 * @tags reliability correctness
 */

import cpp

predicate isPmRuntimeGetSync(FunctionCall fc) {
  fc.getTarget().getName() = "pm_runtime_get_sync" or
  fc.getTarget().getName() = "pm_runtime_resume_and_get"
}

predicate isPmRuntimePut(FunctionCall fc) {
  fc.getTarget().getName() = "pm_runtime_put" or
  fc.getTarget().getName() = "pm_runtime_put_sync" or
  fc.getTarget().getName() = "pm_runtime_put_noidle" or
  fc.getTarget().getName() = "pm_runtime_put_autosuspend"
}

predicate errorReturnAfterGet(FunctionCall getCall, ReturnStmt ret) {
  exists(IfStmt ifs |
    ifs.getEnclosingFunction() = getCall.getEnclosingFunction() and
    ret.getEnclosingStmt*() = ifs.getThen() and
    getCall.getLocation().getStartLine() < ifs.getLocation().getStartLine() and
    getCall.getEnclosingFunction() = ret.getEnclosingFunction()
  )
}

predicate noPutBeforeReturn(FunctionCall getCall, ReturnStmt ret) {
  not exists(FunctionCall putCall |
    isPmRuntimePut(putCall) and
    putCall.getEnclosingFunction() = getCall.getEnclosingFunction() and
    putCall.getLocation().getStartLine() < ret.getLocation().getStartLine() and
    putCall.getLocation().getStartLine() > getCall.getLocation().getStartLine()
  )
}

from FunctionCall getCall, ReturnStmt ret
where
  isPmRuntimeGetSync(getCall) and
  errorReturnAfterGet(getCall, ret) and
  noPutBeforeReturn(getCall, ret)
select getCall,
  "pm_runtime_get_sync at this call site has an error-return path at " +
  ret.getLocation().toString() +
  " that does not call pm_runtime_put, leaking the runtime PM usage counter."
