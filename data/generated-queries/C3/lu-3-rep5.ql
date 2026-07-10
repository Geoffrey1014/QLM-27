/**
 * @name pm_runtime_get_sync refcount leak on error return
 * @description pm_runtime_get_sync increments the runtime-PM usage counter
 *              even when it returns an error. Returning on the error branch
 *              without calling pm_runtime_put leaks the reference.
 * @kind problem
 * @problem.severity warning
 * @id qlm/pm-runtime-refcount-leak-on-error-lu3-rep5
 */

import cpp

predicate isAcquire(FunctionCall fc) {
  fc.getTarget().getName() = "pm_runtime_get_sync"
}

predicate isRelease(FunctionCall fc, Expr devArg) {
  (fc.getTarget().getName() = "pm_runtime_put" or
   fc.getTarget().getName() = "pm_runtime_put_sync" or
   fc.getTarget().getName() = "pm_runtime_put_noidle" or
   fc.getTarget().getName() = "pm_runtime_put_autosuspend") and
  devArg = fc.getArgument(0)
}

predicate errorReturnAfterAcquire(FunctionCall acq, ReturnStmt ret) {
  isAcquire(acq) and
  ret.getEnclosingFunction() = acq.getEnclosingFunction() and
  exists(IfStmt ifs |
    ifs.getEnclosingFunction() = acq.getEnclosingFunction() and
    (ret = ifs.getThen() or ret.getParent+() = ifs.getThen()) and
    ifs.getLocation().getStartLine() > acq.getLocation().getStartLine() and
    ifs.getLocation().getStartLine() <= acq.getLocation().getStartLine() + 3
  )
}

predicate noReleaseBeforeReturn(FunctionCall acq, ReturnStmt ret) {
  errorReturnAfterAcquire(acq, ret) and
  not exists(FunctionCall rel |
    isRelease(rel, _) and
    rel.getEnclosingFunction() = acq.getEnclosingFunction() and
    rel.getLocation().getStartLine() < ret.getLocation().getStartLine() and
    rel.getLocation().getStartLine() > acq.getLocation().getStartLine()
  )
}

from FunctionCall acq, ReturnStmt ret
where noReleaseBeforeReturn(acq, ret)
select acq,
  "pm_runtime_get_sync without matching pm_runtime_put on error path (return at line " +
  ret.getLocation().getStartLine() + ")"
