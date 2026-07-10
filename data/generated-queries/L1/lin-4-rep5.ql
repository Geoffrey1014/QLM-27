/**
 * @name Missing of_node_put after device_node acquisition
 * @description Device_node returned by of_parse_phandle and friends must be
 *              released via of_node_put on all return paths, else the node's
 *              refcount leaks.
 * @kind problem
 * @problem.severity warning
 * @id cpp/linux/of-node-put-refcount-leak-lin4-rep5
 */

import cpp

predicate isDeviceNodeAcquisition(FunctionCall fc) {
  fc.getTarget().getName() in [
    "of_parse_phandle",
    "of_find_node_by_name",
    "of_find_node_by_path",
    "of_get_child_by_name",
    "of_find_compatible_node",
    "of_get_next_child",
    "of_get_parent",
    "of_get_next_available_child",
    "of_get_next_parent",
    "of_find_node_by_phandle"
  ]
}

from FunctionCall acquire, Variable v, Function f
where isDeviceNodeAcquisition(acquire)
  and f = acquire.getEnclosingFunction()
  and exists(AssignExpr assign |
        assign.getRValue() = acquire and
        v = assign.getLValue().(VariableAccess).getTarget())
  and exists(ReturnStmt rs |
        rs.getEnclosingFunction() = f and
        not exists(FunctionCall putCall, VariableAccess va |
              putCall.getTarget().getName() = "of_node_put" and
              putCall.getEnclosingFunction() = f and
              va = putCall.getArgument(0) and
              va.getTarget() = v and
              va.getLocation().getStartLine() < rs.getLocation().getStartLine()))
  and not f.getName().toLowerCase().matches("%fixed%")
select acquire,
  "Call to " + acquire.getTarget().getName() +
    " stores result in '" + v.getName() +
    "' but at least one return path in " + f.getName() +
    " does not call of_node_put(), causing a device node reference count leak"
