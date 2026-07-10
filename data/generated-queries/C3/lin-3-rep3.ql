/**
 * @name C3 generated query for lin-3 / fix bf4a9b2467b7
 * @description Missing of_node_put on error path after of_parse_phandle — device_node refcount leak (CWE-772)
 * @kind problem
 * @problem.severity warning
 * @id cpp/rq3/c3/lin-3-rep3
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

predicate hasEarlyReturnBeforePut(FunctionCall acquire, Variable v) {
  exists(ReturnStmt rs |
    rs.getEnclosingFunction() = acquire.getEnclosingFunction() and
    acquire.getLocation().getStartLine() < rs.getLocation().getStartLine() and
    not exists(FunctionCall putCall |
      isOfNodePut(putCall) and
      putCall.getEnclosingFunction() = acquire.getEnclosingFunction() and
      exists(VariableAccess va |
        va = putCall.getArgument(0) and
        va.getTarget() = v
      ) and
      putCall.getLocation().getStartLine() < rs.getLocation().getStartLine()
    )
  )
}

predicate isInFixedFunction(FunctionCall fc) {
  fc.getEnclosingFunction().getName().toLowerCase().matches("%fixed%")
}

from FunctionCall acquire, Variable acquiredVar
where
  isDeviceNodeAcquisition(acquire) and
  acquiredVar = getAcquiredVariable(acquire) and
  hasEarlyReturnBeforePut(acquire, acquiredVar) and
  not isInFixedFunction(acquire)
select acquire,
  "Call to " + acquire.getTarget().getName() +
    " stores result in '" + acquiredVar.getName() +
    "' but a return statement exits before of_node_put() on the error path, leaking the device_node reference"
