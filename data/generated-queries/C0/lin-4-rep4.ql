/**
 * @name Missing of_node_put on error path after of_parse_phandle family
 * @description A device_node pointer obtained from an of_* phandle/child-acquiring
 *              helper has its refcount incremented. If the function returns on an
 *              error path without calling of_node_put() on it, the refcount leaks.
 * @kind problem
 * @problem.severity warning
 * @id cpp/of-node-refcount-leak-on-error
 * @tags reliability
 *       correctness
 *       refcount
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph
import semmle.code.cpp.controlflow.StackVariableReachability

/**
 * Functions in the of_* family that return a `struct device_node *` with the
 * refcount incremented and therefore require an of_node_put() on the result.
 */
predicate isOfNodeAcquirer(Function f) {
  f.getName() in [
      "of_parse_phandle",
      "of_parse_phandle_with_args",
      "of_parse_phandle_with_fixed_args",
      "of_find_node_by_name",
      "of_find_node_by_path",
      "of_find_node_by_phandle",
      "of_find_node_by_type",
      "of_find_compatible_node",
      "of_find_matching_node",
      "of_find_matching_node_and_match",
      "of_find_node_with_property",
      "of_get_parent",
      "of_get_next_parent",
      "of_get_child_by_name",
      "of_get_next_child",
      "of_get_next_available_child",
      "of_get_next_cpu_node",
      "of_get_compatible_child",
      "of_get_cpu_node",
      "of_graph_get_next_endpoint",
      "of_graph_get_remote_endpoint",
      "of_graph_get_remote_node",
      "of_graph_get_remote_port",
      "of_graph_get_remote_port_parent",
      "of_graph_get_port_by_id",
      "of_irq_find_parent"
    ]
}

/** A call to a function that releases the refcount on a device_node. */
predicate isOfNodeReleaser(FunctionCall fc, Variable v) {
  (
    fc.getTarget().getName() = "of_node_put" or
    fc.getTarget().getName() = "of_node_put_kobj"
  ) and
  fc.getArgument(0).(VariableAccess).getTarget() = v
}

/**
 * Holds if `node` is a local variable assigned the result of an of_* acquirer
 * call `acq`, in function `f`.
 */
predicate acquiredNode(LocalScopeVariable node, FunctionCall acq, Function f) {
  isOfNodeAcquirer(acq.getTarget()) and
  acq.getEnclosingFunction() = f and
  (
    // direct assignment: node = of_parse_phandle(...)
    exists(AssignExpr a |
      a.getLValue().(VariableAccess).getTarget() = node and
      a.getRValue() = acq
    )
    or
    // initialization: struct device_node *node = of_parse_phandle(...)
    exists(Initializer init |
      init.getDeclaration() = node and
      init.getExpr() = acq
    )
  ) and
  node.getType().getUnspecifiedType().(PointerType).getBaseType().getName() = "device_node"
}

/**
 * Holds if there is a control-flow path from `acq` to a `ReturnStmt` `ret`
 * inside function `f`, without an intervening call to of_node_put(node).
 */
predicate leaksOnReturn(FunctionCall acq, LocalScopeVariable node, ReturnStmt ret, Function f) {
  acquiredNode(node, acq, f) and
  ret.getEnclosingFunction() = f and
  acq.getASuccessor+() = ret and
  not exists(FunctionCall rel |
    isOfNodeReleaser(rel, node) and
    rel.getEnclosingFunction() = f and
    acq.getASuccessor+() = rel and
    rel.getASuccessor+() = ret
  ) and
  // restrict to error returns: returning a non-null integer constant, or
  // returning a propagated error value (heuristic: the ReturnStmt is guarded
  // by a condition checking for failure of some prior call).
  (
    exists(Expr re | re = ret.getExpr() |
      re.getValue().toInt() != 0
      or
      // returning a variable likely holding an error code (-E*)
      re instanceof VariableAccess
      or
      // returning -EXXX (UnaryOperation on integer)
      re instanceof UnaryOperation
    )
  )
}

from FunctionCall acq, LocalScopeVariable node, ReturnStmt ret, Function f
where
  leaksOnReturn(acq, node, ret, f) and
  // Exclude returns that occur AFTER the node has been stored into a long-lived
  // structure (heuristic: ignore if of_node_get is also called, suggesting
  // intentional ownership transfer).
  not exists(FunctionCall xfer |
    xfer.getEnclosingFunction() = f and
    xfer.getTarget().getName() = "of_node_get" and
    xfer.getArgument(0).(VariableAccess).getTarget() = node
  )
select ret,
  "Possible refcount leak: device_node acquired by $@ may not be released on this error return path.",
  acq, acq.getTarget().getName()
