/**
 * @name pm_runtime_get_sync refcount leak on error path
 * @description pm_runtime_get_sync increments the runtime PM usage counter
 *   even on failure; an error-path return without pm_runtime_put leaks the
 *   refcount.
 * @kind problem
 * @problem.severity warning
 * @id cpp/pm-runtime-get-sync-refcount-leak
 */

import cpp

predicate isAcquireCall(FunctionCall fc) {
  fc.getTarget().getName() = "pm_runtime_get_sync"
}

predicate isReleaseCall(FunctionCall fc) {
  fc.getTarget().getName() = "pm_runtime_put" or
  fc.getTarget().getName() = "pm_runtime_put_noidle" or
  fc.getTarget().getName() = "pm_runtime_put_sync"
}

predicate errorReturnAfterAcquire(FunctionCall acq, ReturnStmt rs) {
  isAcquireCall(acq) and
  rs.getEnclosingFunction() = acq.getEnclosingFunction() and
  exists(IfStmt ifs | ifs.getThen().getAChild*() = rs or ifs.getThen() = rs) and
  rs.getLocation().getStartLine() > acq.getLocation().getStartLine()
}

predicate noReleaseBeforeReturn(FunctionCall acq, ReturnStmt rs) {
  errorReturnAfterAcquire(acq, rs) and
  not exists(FunctionCall rel |
    isReleaseCall(rel) and
    rel.getEnclosingFunction() = acq.getEnclosingFunction() and
    rel.getLocation().getStartLine() > acq.getLocation().getStartLine() and
    rel.getLocation().getStartLine() < rs.getLocation().getStartLine()
  )
}

from FunctionCall acq, ReturnStmt rs
where noReleaseBeforeReturn(acq, rs)
select acq, "pm_runtime_get_sync refcount leak: error path returns without pm_runtime_put"
