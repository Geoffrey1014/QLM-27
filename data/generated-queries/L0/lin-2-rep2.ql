/**
 * @name Refcount leak on of_node acquired via for_each_available_child_of_node
 * @description Detects functions that acquire an of_node reference through
 *              the for_each_available_child_of_node iterator (or one of the
 *              of_get_* / of_find_* / of_parse_phandle family) but do not
 *              release it via of_node_put before an early return / goto exit.
 * @kind problem
 * @problem.severity warning
 * @id qlm/l0/lin-2/of-node-refcount-leak
 */

import cpp

predicate isOfNodeAcquire(FunctionCall fc) {
  fc.getTarget().getName() in [
    "of_find_node_by_path", "of_find_node_opts_by_path",
    "of_find_matching_node", "of_find_compatible_node",
    "of_find_node_by_name", "of_find_node_by_type",
    "of_find_node_by_phandle", "of_get_child_by_name",
    "of_get_next_child", "of_get_next_available_child",
    "of_get_parent", "of_get_next_parent", "of_parse_phandle",
    "__first_child", "__next_child"
  ]
}

from Function f, FunctionCall acq, Variable child
where
  acq.getEnclosingFunction() = f and
  isOfNodeAcquire(acq) and
  (
    child.getAnAccess() = acq.getAnArgument()
    or
    exists(AssignExpr a |
      a.getRValue() = acq and a.getLValue() = child.getAnAccess()
    )
  ) and
  not exists(FunctionCall rel |
    rel.getEnclosingFunction() = f and
    rel.getTarget().getName() = "of_node_put" and
    rel.getAnArgument() = child.getAnAccess()
  )
select acq,
  "Potential refcount leak: of_node acquired but not released via of_node_put in function " +
    f.getName()
