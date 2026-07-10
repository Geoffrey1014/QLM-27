/**
 * @name pm_runtime_get_sync reference count leak on error path
 * @description Detects functions where pm_runtime_get_sync is followed by an
 *              early error return (typically `if (ret < 0) return ret;`) that
 *              does not call any pm_runtime_put* variant, leaking the
 *              PM runtime usage counter that get_sync increments even on
 *              failure. Pattern originates from Qiushi Wu (Lu group) fix
 *              f141a422159a in sound/soc/rockchip/rockchip_pdm.c.
 * @kind problem
 * @problem.severity warning
 * @id qlm/l0/lu-3-rep5/pm-runtime-get-sync-leak
 */

import cpp

predicate isPmRuntimeGetSync(FunctionCall fc) {
  fc.getTarget().getName() = "pm_runtime_get_sync"
}

from FunctionCall acquire, IfStmt errIf, ReturnStmt ret
where
  isPmRuntimeGetSync(acquire) and
  errIf.getEnclosingFunction() = acquire.getEnclosingFunction() and
  ret.getEnclosingFunction() = acquire.getEnclosingFunction() and
  ret.getEnclosingElement*() = errIf.getThen() and
  errIf.getLocation().getStartLine() > acquire.getLocation().getStartLine() and
  not exists(FunctionCall release |
    release.getEnclosingFunction() = acquire.getEnclosingFunction() and
    release.getTarget().getName() in [
      "pm_runtime_put", "pm_runtime_put_sync",
      "pm_runtime_put_noidle", "pm_runtime_put_autosuspend"
    ] and
    release.getEnclosingElement*() = errIf.getThen()
  )
select acquire,
  "pm_runtime_get_sync error path returns without pm_runtime_put*, causing refcount leak"
