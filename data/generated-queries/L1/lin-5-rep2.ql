/**
 * @name L1 generated query for lin-5 / fix 10d6bdf53290
 * @description Missing put_device after of_find_device_by_node — platform_device refcount leak (CWE-772)
 * @kind problem
 * @problem.severity warning
 * @id cpp/rq3/l1/lin-5-rep2
 */

import cpp

predicate isPlatformDeviceAcquisition(FunctionCall fc) {
  fc.getTarget().getName() = "of_find_device_by_node"
}

predicate hasMatchingPutDevice(FunctionCall acquire, Variable v) {
  exists(FunctionCall putCall |
    putCall.getTarget().getName() = "put_device" and
    putCall.getEnclosingFunction() = acquire.getEnclosingFunction() and
    exists(VariableAccess va |
      va.getTarget() = v and
      putCall.getAnArgument().getAChild*() = va
    )
  )
}

from FunctionCall acquire, Variable v
where
  isPlatformDeviceAcquisition(acquire) and
  exists(AssignExpr assign |
    assign.getRValue() = acquire and
    v = assign.getLValue().(VariableAccess).getTarget()
  ) and
  exists(IfStmt ifStmt, VariableAccess va |
    ifStmt.getEnclosingFunction() = acquire.getEnclosingFunction() and
    va.getTarget() = v and
    ifStmt.getCondition().getAChild*() = va
  ) and
  not hasMatchingPutDevice(acquire, v) and
  not acquire.getEnclosingFunction().getName().toLowerCase().matches("%fixed%")
select acquire,
  "Call to " + acquire.getTarget().getName() +
    " stores platform_device in '" + v.getName() +
    "' but put_device() is never called on it, causing a refcount leak (CWE-772)"
