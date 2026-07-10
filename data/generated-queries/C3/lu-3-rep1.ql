/**
 * @name pm_runtime_get_sync refcount leak on error path
 * @description pm_runtime_get_sync increments the runtime-PM usage counter
 *              even when it returns an error. Failing to call pm_runtime_put
 *              on the error branch leaks the reference.
 * @kind problem
 * @problem.severity warning
 * @id qlm/pm-runtime-refcount-leak-on-error
 */

import cpp

predicate isPmGetSync(FunctionCall fc) {
  fc.getTarget().getName() = "pm_runtime_get_sync"
}

predicate isPmPut(FunctionCall fc) {
  fc.getTarget().getName() in [
    "pm_runtime_put", "pm_runtime_put_sync",
    "pm_runtime_put_noidle", "pm_runtime_put_autosuspend"
  ]
}

predicate errorBranchLeaks(FunctionCall get, IfStmt ifs) {
  isPmGetSync(get) and
  ifs.getEnclosingFunction() = get.getEnclosingFunction() and
  exists(Variable v |
    v.getAnAssignedValue() = get and
    ifs.getCondition().getAChild*().(VariableAccess).getTarget() = v
  ) and
  exists(ReturnStmt r |
    r.getEnclosingStmt+() = ifs.getThen() or r = ifs.getThen()
  ) and
  not exists(FunctionCall put |
    isPmPut(put) and
    (put.getEnclosingStmt().getParentStmt*() = ifs.getThen() or
     put.getEnclosingStmt() = ifs.getThen())
  )
}

from FunctionCall get, IfStmt ifs
where errorBranchLeaks(get, ifs)
select get,
  "pm_runtime_get_sync return value tested at " + ifs.getLocation().toString() +
  " but error branch returns without pm_runtime_put — refcount leak"
