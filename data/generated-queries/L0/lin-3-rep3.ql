/**
 * @name L0 generated query for lin-3 rep3 / fix bf4a9b2467b7
 * @description Missing of_node_put after of_parse_phandle - device_node refcount leak (CWE-401)
 * @kind problem
 * @problem.severity warning
 * @id cpp/rq3/l0/lin-3-rep3
 */

import cpp

predicate isDeviceNodeLeak(FunctionCall acquire, Variable acquiredVar) {
  acquire.getTarget().getName() in [
    "of_parse_phandle",
    "of_find_node_by_name",
    "of_find_node_by_path",
    "of_get_child_by_name",
    "of_find_compatible_node",
    "of_get_parent",
    "of_get_next_child"
  ] and
  exists(AssignExpr assign |
    assign.getRValue() = acquire and
    acquiredVar = assign.getLValue().(VariableAccess).getTarget()
  ) and
  not exists(FunctionCall putCall, VariableAccess va |
    putCall.getTarget().getName() = "of_node_put" and
    putCall.getEnclosingFunction() = acquire.getEnclosingFunction() and
    va = putCall.getArgument(0) and
    va.getTarget() = acquiredVar
  ) and
  not acquire.getEnclosingFunction().getName().toLowerCase().matches("%fixed%")
}

from FunctionCall acquire, Variable acquiredVar
where isDeviceNodeLeak(acquire, acquiredVar)
select acquire,
  "Call to " + acquire.getTarget().getName() +
    " stores result in '" + acquiredVar.getName() +
    "' but of_node_put() is never called, causing a device node reference count leak"
