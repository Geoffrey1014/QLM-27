/**
 * @name L0 generated query for lin-4 / fix 1332661e0930
 * @description Missing of_node_put after of_parse_phandle — device_node refcount leak (CWE-772)
 * @kind problem
 * @problem.severity warning
 * @id cpp/rq3/l0/lin-4-rep5
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

from FunctionCall acquire, Variable v
where
  isDeviceNodeAcquisition(acquire) and
  exists(AssignExpr assign |
    assign.getRValue() = acquire and
    v = assign.getLValue().(VariableAccess).getTarget()
  ) and
  exists(IfStmt ifStmt, VariableAccess va |
    ifStmt.getEnclosingFunction() = acquire.getEnclosingFunction() and
    va.getTarget() = v and
    ifStmt.getCondition().getAChild*() = va
  ) and
  not exists(FunctionCall putCall, VariableAccess va |
    putCall.getTarget().getName() = "of_node_put" and
    putCall.getEnclosingFunction() = acquire.getEnclosingFunction() and
    va = putCall.getArgument(0) and
    va.getTarget() = v
  ) and
  not acquire.getEnclosingFunction().getName().toLowerCase().matches("%fixed%")
select acquire,
  "Call to " + acquire.getTarget().getName() +
    " stores result in '" + v.getName() +
    "' but of_node_put() is never called, causing a device node reference count leak"
