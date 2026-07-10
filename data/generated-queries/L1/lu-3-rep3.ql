/**
 * @name pm_runtime_get_sync reference count leak on error path
 * @description Detects rockchip-style bugs where pm_runtime_get_sync's
 *              error branch returns without calling pm_runtime_put*,
 *              leaking the PM runtime reference count.
 * @kind problem
 * @problem.severity warning
 * @id qlllm/pm-runtime-refcount-leak-lu-3
 */

import cpp

predicate isPmGetSync(FunctionCall fc) {
  fc.getTarget().getName() = "pm_runtime_get_sync"
}

predicate returnsWithoutPut(FunctionCall acq, ReturnStmt ret) {
  isPmGetSync(acq) and
  ret.getEnclosingFunction() = acq.getEnclosingFunction() and
  exists(IfStmt ifs |
    ifs.getEnclosingFunction() = acq.getEnclosingFunction() and
    ret.getParent*() = ifs.getThen() and
    ifs.getLocation().getStartLine() > acq.getLocation().getStartLine() and
    ret.getLocation().getStartLine() > acq.getLocation().getStartLine() and
    not exists(FunctionCall putCall |
      putCall.getEnclosingFunction() = acq.getEnclosingFunction() and
      putCall.getTarget().getName().matches("pm_runtime_put%") and
      putCall.getParent*() = ifs.getThen()
    )
  )
}

from FunctionCall acq, ReturnStmt ret
where returnsWithoutPut(acq, ret)
select acq, "pm_runtime_get_sync may leak refcount: error-path return at $@ without pm_runtime_put", ret, ret.toString()
