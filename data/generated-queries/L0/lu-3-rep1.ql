/**
 * @name pm_runtime_get_sync refcount leak on error return
 * @description Detects functions that call pm_runtime_get_sync, take an
 *              error-return path when the call fails, and never call
 *              pm_runtime_put on that error path. pm_runtime_get_sync
 *              increments the runtime-PM usage counter even on failure,
 *              so the counter is leaked unless the caller explicitly
 *              drops it on the error path.
 * @kind problem
 * @problem.severity warning
 * @id qlm/l0-lu3-pm-runtime-get-sync-leak
 */
import cpp

predicate isAcquireCall(FunctionCall fc) {
  fc.getTarget().getName() = "pm_runtime_get_sync"
}

from FunctionCall acquire, Function enclosing, IfStmt guard, ReturnStmt errRet
where isAcquireCall(acquire)
  and enclosing = acquire.getEnclosingFunction()
  and guard.getEnclosingFunction() = enclosing
  and errRet.getEnclosingFunction() = enclosing
  and errRet.getParent+() = guard.getThen()
  and not exists(FunctionCall put |
        put.getTarget().getName().matches("pm_runtime_put%") and
        put.getEnclosingFunction() = enclosing and
        put.getParent+() = guard.getThen()
      )
select acquire,
  "pm_runtime_get_sync in '" + enclosing.getName() +
  "' has an error-return path (IfStmt at " + guard.getLocation().toString() +
  ") that does not call pm_runtime_put; runtime-PM refcount is leaked on failure."
