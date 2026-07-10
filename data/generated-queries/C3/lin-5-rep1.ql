/**
 * @name C3 generated query for lin-5 / fix 10d6bdf53290
 * @description Missing put_device after of_find_device_by_node — platform_device refcount leak (CWE-911)
 * @kind problem
 * @problem.severity warning
 * @id cpp/rq3/c3/lin-5-rep1
 */

import cpp

predicate isPlatformDeviceAcquisition(FunctionCall fc) {
  fc.getTarget().getName() in [
    "of_find_device_by_node",
    "bus_find_device_by_name",
    "bus_find_device_by_of_node",
    "driver_find_device_by_name",
    "class_find_device_by_name"
  ]
}

predicate isPutDevice(FunctionCall fc) {
  fc.getTarget().getName() = "put_device"
}

Variable getAcquiredVariable(FunctionCall acquire) {
  exists(AssignExpr assign |
    assign.getRValue() = acquire and
    result = assign.getLValue().(VariableAccess).getTarget()
  )
}

predicate hasMatchingPutDevice(FunctionCall acquire, Variable v) {
  exists(FunctionCall putCall |
    isPutDevice(putCall) and
    putCall.getEnclosingFunction() = acquire.getEnclosingFunction() and
    exists(VariableAccess va |
      putCall.getArgument(0).getAChild*() = va and
      va.getTarget() = v
    )
  )
}

predicate hasNullCheck(FunctionCall acquire, Variable v) {
  exists(IfStmt ifStmt, VariableAccess va |
    ifStmt.getEnclosingFunction() = acquire.getEnclosingFunction() and
    va.getTarget() = v and
    ifStmt.getCondition().getAChild*() = va
  )
}

predicate isInFixedFunction(FunctionCall fc) {
  fc.getEnclosingFunction().getName().toLowerCase().matches("%fixed%")
}

from FunctionCall acquire, Variable acquiredVar
where
  isPlatformDeviceAcquisition(acquire) and
  acquiredVar = getAcquiredVariable(acquire) and
  hasNullCheck(acquire, acquiredVar) and
  not hasMatchingPutDevice(acquire, acquiredVar) and
  not isInFixedFunction(acquire)
select acquire,
  "Call to " + acquire.getTarget().getName() +
    " stores result in '" + acquiredVar.getName() +
    "' but put_device(&" + acquiredVar.getName() + "->dev) is never called, causing a platform_device refcount leak"
