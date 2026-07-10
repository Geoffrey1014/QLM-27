/**
 * @name L0 generated query for lu-3 / fix f141a422159a
 * @description pm_runtime_get_sync increments the runtime-PM usage counter even
 *              when it returns a negative error code. An error-handling path
 *              that simply returns the error without calling pm_runtime_put
 *              leaks the counter (CWE-911). Detects call sites whose
 *              early-error return path lacks a balancing pm_runtime_put.
 * @kind problem
 * @problem.severity warning
 * @id cpp/rq3/l0/lu-3-rep4
 * @tags reliability correctness
 */

import cpp

predicate hasRefcountLeakOnError(FunctionCall getCall, ReturnStmt ret) {
  (
    getCall.getTarget().getName() = "pm_runtime_get_sync" or
    getCall.getTarget().getName() = "pm_runtime_resume_and_get"
  ) and
  exists(IfStmt ifs |
    ifs.getEnclosingFunction() = getCall.getEnclosingFunction() and
    ret.getEnclosingStmt*() = ifs.getThen() and
    getCall.getLocation().getStartLine() < ifs.getLocation().getStartLine() and
    ret.getEnclosingFunction() = getCall.getEnclosingFunction()
  ) and
  not exists(FunctionCall putCall |
    (
      putCall.getTarget().getName() = "pm_runtime_put" or
      putCall.getTarget().getName() = "pm_runtime_put_sync" or
      putCall.getTarget().getName() = "pm_runtime_put_noidle" or
      putCall.getTarget().getName() = "pm_runtime_put_autosuspend"
    ) and
    putCall.getEnclosingFunction() = getCall.getEnclosingFunction() and
    putCall.getLocation().getStartLine() > getCall.getLocation().getStartLine() and
    putCall.getLocation().getStartLine() < ret.getLocation().getStartLine()
  ) and
  not getCall.getEnclosingFunction().getName().toLowerCase().matches("%fixed%")
}

from FunctionCall getCall, ReturnStmt ret
where hasRefcountLeakOnError(getCall, ret)
select getCall,
  "pm_runtime_get_sync at this call site has an error-return path at " +
  ret.getLocation().toString() +
  " that does not call pm_runtime_put, leaking the runtime PM usage counter."
