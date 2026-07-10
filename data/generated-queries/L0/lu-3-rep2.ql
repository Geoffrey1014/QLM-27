/**
 * @name Missing pm_runtime_put after failing pm_runtime_get_sync (refcount leak)
 * @description Detects functions that call pm_runtime_get_sync (or
 *              pm_runtime_resume_and_get), test its return value in an
 *              if-statement, return early from that if-branch, and do
 *              NOT invoke a matching pm_runtime_put* on that error
 *              path. pm_runtime_get_sync increments the PM runtime
 *              refcount even on failure, so the error path must call
 *              pm_runtime_put to balance it (CWE-911, refcount leak).
 *              Pattern origin: commit f141a422159a
 *              "ASoC: rockchip: Fix a reference count leak.".
 * @kind problem
 * @problem.severity warning
 * @id qlm/l0-lu3-pm-runtime-refcount-leak
 */
import cpp

predicate isPmRuntimeGetSync(FunctionCall fc) {
  fc.getTarget().getName() in [
    "pm_runtime_get_sync",
    "pm_runtime_resume_and_get"
  ]
}

from FunctionCall acquire, Function enclosing, Variable ret, IfStmt ifs, ReturnStmt returnStmt
where isPmRuntimeGetSync(acquire)
  and enclosing = acquire.getEnclosingFunction()
  and exists(AssignExpr ae |
    ae.getRValue() = acquire and
    ae.getLValue() = ret.getAnAccess()
  )
  and ifs.getEnclosingFunction() = enclosing
  and ifs.getCondition().getAChild*() = ret.getAnAccess()
  and returnStmt.getEnclosingStmt*() = ifs.getThen()
  and not exists(FunctionCall put |
    put.getEnclosingFunction() = enclosing and
    put.getTarget().getName() in [
      "pm_runtime_put", "pm_runtime_put_sync",
      "pm_runtime_put_noidle", "pm_runtime_put_autosuspend",
      "pm_runtime_put_sync_autosuspend", "pm_runtime_put_sync_suspend"
    ] and
    put.getEnclosingStmt().getEnclosingStmt*() = ifs.getThen()
  )
  and not enclosing.getName().toLowerCase().matches("%fixed%")
select acquire,
  "pm_runtime_get_sync in '" + enclosing.getName() +
  "' has no matching pm_runtime_put on the error path guarded by '" +
  ret.getName() + " < 0' (refcount leak; CWE-911)."
