/**
 * @name pm_runtime_get_sync reference count leak (error path)
 * @description Detects functions where pm_runtime_get_sync is followed by
 *              an error-branch return without a balancing pm_runtime_put,
 *              causing a runtime PM reference count leak. Mirrors the bug
 *              fixed in commit f141a422159a (ASoC: rockchip: rockchip_pdm).
 * @id cpp/pm-runtime-get-sync-leak
 * @kind problem
 * @problem.severity warning
 */

import cpp

predicate isPmGetSync(FunctionCall fc) {
  fc.getTarget().getName() = "pm_runtime_get_sync"
}

predicate isPmPut(FunctionCall fc) {
  fc.getTarget().getName() = ["pm_runtime_put", "pm_runtime_put_sync",
                              "pm_runtime_put_noidle", "pm_runtime_put_autosuspend"]
}

predicate errorBranchReturn(FunctionCall get, ReturnStmt ret) {
  isPmGetSync(get) and
  exists(IfStmt ifs |
    ifs.getEnclosingFunction() = get.getEnclosingFunction() and
    ret.getEnclosingFunction() = get.getEnclosingFunction() and
    get.getLocation().getStartLine() < ifs.getLocation().getStartLine() and
    (ret = ifs.getThen() or ret.getParent+() = ifs.getThen())
  )
}

predicate noPutBetween(FunctionCall get, ReturnStmt ret) {
  errorBranchReturn(get, ret) and
  not exists(FunctionCall put |
    isPmPut(put) and
    put.getEnclosingFunction() = get.getEnclosingFunction() and
    put.getLocation().getStartLine() >= get.getLocation().getStartLine() and
    put.getLocation().getStartLine() <= ret.getLocation().getStartLine()
  )
}

from FunctionCall get, ReturnStmt ret
where noPutBetween(get, ret)
select get,
  "pm_runtime_get_sync reference count leak: error path returns without pm_runtime_put (return at $@).",
  ret, ret.toString()
