/**
 * @name C3 generated query for lin-1 / fix 74139a64e8ce
 * @description Missing of_node_put after of_parse_phandle — device_node refcount leak (CWE-401)
 * @kind problem
 * @problem.severity warning
 * @id cpp/rq3/c3/lin-1-rep1
 */

import cpp

predicate isDeviceNodeAcquisition(FunctionCall fc) {
  fc.getTarget().getName() in [
    "of_parse_phandle",
    "of_find_node_by_name",
    "of_find_node_by_path",
    "of_get_child_by_name",
    "of_find_compatible_node"
  ]
}

predicate isOfNodePut(FunctionCall fc) {
  fc.getTarget().getName() = "of_node_put"
}

Variable getAcquiredVariable(FunctionCall acquire) {
  exists(AssignExpr assign |
    assign.getRValue() = acquire and
    result = assign.getLValue().(VariableAccess).getTarget()
  )
}

predicate hasMatchingOfNodePut(FunctionCall acquire, Variable v) {
  exists(FunctionCall putCall |
    isOfNodePut(putCall) and
    putCall.getEnclosingFunction() = acquire.getEnclosingFunction() and
    exists(VariableAccess va |
      va = putCall.getArgument(0) and
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
  isDeviceNodeAcquisition(acquire) and
  acquiredVar = getAcquiredVariable(acquire) and
  hasNullCheck(acquire, acquiredVar) and
  not hasMatchingOfNodePut(acquire, acquiredVar) and
  not isInFixedFunction(acquire)
select acquire,
  "Call to " + acquire.getTarget().getName() +
    " stores result in '" + acquiredVar.getName() +
    "' but of_node_put() is never called, causing a device node reference count leak"
