/**
 * @name L0 generated query for lu-3 / fix f141a422159a
 * @description pm_runtime_get_sync reference count leak: error path returns
 *              without calling pm_runtime_put (mirrors ASoC: rockchip fix
 *              f141a422159a). CWE-911.
 * @kind problem
 * @problem.severity warning
 * @id cpp/rq3/l0/lu-3-rep3
 */

import cpp

predicate hasPmRuntimeGetSyncLeak(FunctionCall get, ReturnStmt ret) {
  get.getTarget().getName() = "pm_runtime_get_sync" and
  exists(IfStmt ifs |
    ifs.getEnclosingFunction() = get.getEnclosingFunction() and
    ret.getEnclosingFunction() = get.getEnclosingFunction() and
    get.getLocation().getStartLine() < ifs.getLocation().getStartLine() and
    (ret = ifs.getThen() or ret.getParent+() = ifs.getThen())
  ) and
  not exists(FunctionCall put |
    put.getTarget().getName() = ["pm_runtime_put", "pm_runtime_put_sync",
                                  "pm_runtime_put_noidle", "pm_runtime_put_autosuspend"] and
    put.getEnclosingFunction() = get.getEnclosingFunction() and
    put.getLocation().getStartLine() >= get.getLocation().getStartLine() and
    put.getLocation().getStartLine() <= ret.getLocation().getStartLine()
  )
}

from FunctionCall get, ReturnStmt ret
where hasPmRuntimeGetSyncLeak(get, ret)
select get,
  "pm_runtime_get_sync reference count leak: error path returns without pm_runtime_put (return at $@).",
  ret, ret.toString()
