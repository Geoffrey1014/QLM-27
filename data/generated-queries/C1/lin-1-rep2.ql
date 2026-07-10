/**
 * @name Missing of_node_put on device_node acquired in a loop
 * @description Detects loops that acquire a device_node reference via a
 *              refcount-bumping API (of_parse_phandle, of_find_node_by_name,
 *              of_get_child_by_name, etc.) but fail to release it via
 *              of_node_put() on one or more loop-body exit paths
 *              (continue / break / fallthrough to next iteration).
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-lin-1
 * @tags correctness
 *       resource-leak
 */

import cpp

/** Functions that return a device_node* with an incremented refcount. */
predicate refAcquiringCall(FunctionCall fc) {
  fc.getTarget().getName() in [
    "of_parse_phandle",
    "of_find_node_by_name",
    "of_find_node_by_path",
    "of_find_node_by_phandle",
    "of_find_compatible_node",
    "of_find_matching_node",
    "of_find_matching_node_and_match",
    "of_get_child_by_name",
    "of_get_next_child",
    "of_get_next_available_child",
    "of_get_parent",
    "of_get_next_parent",
    "of_get_compatible_child",
    "of_irq_find_parent"
  ]
}

/** Stringify exit kind for the message. */
string exitKind(Stmt s) {
  s instanceof ContinueStmt and result = "continue"
  or
  s instanceof BreakStmt and result = "break"
}

from Loop loop, FunctionCall acq, Variable v, Stmt exitStmt, Function f
where
  f = loop.getEnclosingFunction() and
  acq.getEnclosingStmt().getParentStmt*() = loop.getStmt() and
  refAcquiringCall(acq) and
  // v is the variable holding the acquired node
  (
    exists(AssignExpr a |
      a.getRValue() = acq and
      a.getLValue().(VariableAccess).getTarget() = v
    )
    or
    exists(DeclStmt ds, Initializer init |
      ds.getADeclaration() = v and
      v.getInitializer() = init and
      init.getExpr() = acq
    )
  ) and
  // exitStmt is a continue/break inside the loop body that follows the acquire
  exitStmt.getParentStmt*() = loop.getStmt() and
  (exitStmt instanceof ContinueStmt or exitStmt instanceof BreakStmt) and
  acq.getASuccessor*() = exitStmt and
  // No of_node_put(v) call on any path from acq to exitStmt
  not exists(FunctionCall put |
    put.getEnclosingFunction() = f and
    put.getTarget().getName() = "of_node_put" and
    put.getArgument(0).(VariableAccess).getTarget() = v and
    acq.getASuccessor*() = put and
    put.getASuccessor*() = exitStmt
  )
select acq,
  "device_node reference acquired here may leak on a " +
    exitKind(exitStmt) +
    " path; missing of_node_put($@).", v, v.getName()
