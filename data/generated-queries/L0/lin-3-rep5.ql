/**
 * @name Refcount leak: of_parse_phandle without of_node_put on early return
 * @description Detects functions that acquire a device_node via of_parse_phandle
 *              (or similar of_* getters) and have a return path that does not
 *              release the node with of_node_put.
 * @kind problem
 * @problem.severity warning
 * @id qlm/of-node-refcount-leak-lin3-rep5
 */

import cpp

predicate isAcquire(FunctionCall fc) {
  fc.getTarget().getName() = "of_parse_phandle" or
  fc.getTarget().getName() = "of_get_child_by_name" or
  fc.getTarget().getName() = "of_parse_phandle_with_args" or
  fc.getTarget().getName() = "of_get_parent" or
  fc.getTarget().getName() = "of_find_node_by_path" or
  fc.getTarget().getName() = "of_find_compatible_node"
}

from FunctionCall acq, Variable v, ReturnStmt ret, Function f
where
  isAcquire(acq) and
  f = acq.getEnclosingFunction() and
  ret.getEnclosingFunction() = f and
  exists(AssignExpr a |
    a.getRValue() = acq and
    a.getLValue() = v.getAnAccess()
  ) and
  ret.getLocation().getStartLine() > acq.getLocation().getStartLine() and
  not exists(FunctionCall rel |
    rel.getTarget().getName() = "of_node_put" and
    rel.getEnclosingFunction() = f and
    rel.getArgument(0) = v.getAnAccess() and
    rel.getLocation().getStartLine() < ret.getLocation().getStartLine() and
    rel.getLocation().getStartLine() > acq.getLocation().getStartLine()
  )
select acq,
  "Refcount leak: " + v.getName() + " acquired by " + acq.getTarget().getName()
    + " may not be released on early return path."
