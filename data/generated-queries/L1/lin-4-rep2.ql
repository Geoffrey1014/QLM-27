/**
 * @name Refcount leak in of_node acquisition (L1)
 * @description of_parse_phandle and friends return a device_node with an
 *              incremented refcount that must be released with of_node_put.
 *              Flag acquisitions where at least one return path may not release.
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3/lin-4-rep2-L1
 */

import cpp

predicate isOfNodeAcquire(FunctionCall fc) {
  fc.getTarget().getName() in [
    "of_parse_phandle",
    "of_parse_phandle_with_args",
    "of_find_node_by_name",
    "of_find_node_by_path",
    "of_find_node_by_phandle",
    "of_find_compatible_node",
    "of_get_child_by_name",
    "of_get_next_child",
    "of_get_next_available_child",
    "of_get_parent",
    "of_get_next_parent"
  ]
}

from FunctionCall acquire, Variable v, Function enclosing, ReturnStmt ret
where
  isOfNodeAcquire(acquire) and
  enclosing = acquire.getEnclosingFunction() and
  exists(AssignExpr assign |
    assign.getRValue() = acquire and
    v = assign.getLValue().(VariableAccess).getTarget()
  ) and
  ret.getEnclosingFunction() = enclosing and
  acquire.getLocation().getStartLine() < ret.getLocation().getStartLine() and
  not enclosing.getName().toLowerCase().matches("%fixed%") and
  not exists(FunctionCall put |
    put.getTarget().getName() = "of_node_put" and
    put.getEnclosingFunction() = enclosing and
    put.getArgument(0).(VariableAccess).getTarget() = v and
    put.getLocation().getStartLine() < ret.getLocation().getStartLine() and
    put.getLocation().getStartLine() > acquire.getLocation().getStartLine()
  )
select acquire,
  "Refcount leak: '" + acquire.getTarget().getName() +
    "' result in '" + v.getName() +
    "' may leak on return at line " + ret.getLocation().getStartLine().toString()
