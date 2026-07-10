/**
 * @name pm_runtime_get_sync missing pm_runtime_put on error path
 * @description Detects the pattern where pm_runtime_get_sync() is called and
 *              on the error branch (ret < 0) the function returns without
 *              calling pm_runtime_put(), leaking the runtime PM reference
 *              count. Modeled after commit f141a422159a.
 * @kind problem
 * @problem.severity warning
 * @id qlm/pm-runtime-get-sync-refcount-leak
 */

import cpp

predicate isPmRuntimeGetSync(FunctionCall fc) {
  fc.getTarget().getName() = "pm_runtime_get_sync"
}

predicate isPmRuntimePut(FunctionCall fc) {
  fc.getTarget().getName() in [
    "pm_runtime_put",
    "pm_runtime_put_noidle",
    "pm_runtime_put_sync",
    "pm_runtime_put_autosuspend"
  ]
}

from FunctionCall getCall, Function fn, IfStmt ifs, Variable retVar
where
  isPmRuntimeGetSync(getCall) and
  fn = getCall.getEnclosingFunction() and
  ifs.getEnclosingFunction() = fn and
  // retVar = pm_runtime_get_sync(...)
  retVar.getAnAssignedValue() = getCall and
  // condition is "retVar < 0" (or similar with 0 literal)
  exists(RelationalOperation rel |
    rel = ifs.getCondition().getAChild*() and
    rel.getAnOperand() = retVar.getAnAccess() and
    rel.getAnOperand().(Literal).getValue() = "0"
  ) and
  // then-branch contains a return
  exists(ReturnStmt ret | ret.getEnclosingStmt+() = ifs.getThen()) and
  // no pm_runtime_put in the then-branch
  not exists(FunctionCall putCall |
    isPmRuntimePut(putCall) and
    putCall.getEnclosingStmt+() = ifs.getThen()
  )
select getCall, "pm_runtime_get_sync error path missing pm_runtime_put — refcount leak."
