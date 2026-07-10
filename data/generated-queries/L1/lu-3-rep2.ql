/**
 * @name pm_runtime_get_sync refcount leak on error path
 * @description Detects calls to pm_runtime_get_sync that return < 0 and take an
 *              early-return error branch without a matching pm_runtime_put*.
 *              Pattern seed: f141a422159a (ASoC: rockchip: rockchip_pdm_resume).
 * @kind problem
 * @problem.severity warning
 * @id qlm/l1-lu-3-rep2
 */

import cpp

predicate isPmGetSync(FunctionCall fc) {
  fc.getTarget().getName() = "pm_runtime_get_sync"
}

predicate isPmPutOnErrorPath(FunctionCall get, IfStmt errIf) {
  isPmGetSync(get) and
  errIf.getEnclosingFunction() = get.getEnclosingFunction() and
  exists(FunctionCall put |
    put.getTarget().getName().regexpMatch("pm_runtime_put(_sync|_noidle)?") and
    put.getEnclosingStmt().getParentStmt*() = errIf.getThen()
  )
}

from FunctionCall get, Function f, IfStmt errIf, ReturnStmt r
where
  isPmGetSync(get) and
  f = get.getEnclosingFunction() and
  errIf.getEnclosingFunction() = f and
  errIf.getLocation().getStartLine() > get.getLocation().getStartLine() and
  errIf.getThen().getAChild*() = r and
  not isPmPutOnErrorPath(get, errIf)
select get, "pm_runtime_get_sync without pm_runtime_put on error return in $@", f, f.getName()
