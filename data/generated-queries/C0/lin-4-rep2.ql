/**
 * @name Missing of_node_put on error path after of_* node-acquiring call
 * @description An of_parse_phandle / of_find_node_by_* / of_get_child_by_name
 *              and similar siblings return a device_node with its refcount
 *              incremented. The caller must release it with of_node_put on
 *              every path (including error/early returns). When some error
 *              path returns without calling of_node_put on the acquired
 *              node, the refcount leaks.
 * @kind problem
 * @problem.severity warning
 * @id cpp/of-node-refcount-leak
 * @tags reliability
 *       correctness
 *       resource-leak
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph

/**
 * Functions in the of_* family that acquire a device_node reference
 * which the caller is responsible for releasing via of_node_put.
 */
predicate isOfAcquire(Function f) {
  exists(string n | n = f.getName() |
    n = "of_parse_phandle" or
    n = "of_parse_phandle_with_args" or
    n = "of_parse_phandle_with_fixed_args" or
    n = "of_find_node_by_name" or
    n = "of_find_node_by_path" or
    n = "of_find_node_by_phandle" or
    n = "of_find_node_by_type" or
    n = "of_find_compatible_node" or
    n = "of_find_matching_node" or
    n = "of_find_matching_node_and_match" or
    n = "of_find_node_with_property" or
    n = "of_get_child_by_name" or
    n = "of_get_compatible_child" or
    n = "of_get_next_child" or
    n = "of_get_next_available_child" or
    n = "of_get_parent" or
    n = "of_get_next_parent" or
    n = "of_irq_find_parent" or
    n = "of_cpu_device_node_get" or
    n = "of_graph_get_next_endpoint" or
    n = "of_graph_get_remote_endpoint" or
    n = "of_graph_get_remote_node" or
    n = "of_graph_get_remote_port" or
    n = "of_graph_get_remote_port_parent" or
    n = "of_graph_get_port_by_id"
  )
}

/** A call that releases an of_* device_node reference. */
predicate isOfRelease(FunctionCall fc) {
  fc.getTarget().getName() = "of_node_put"
}

/**
 * `acq` is a call to an of_* acquire function whose returned node is
 * stored in local variable `v` inside enclosing function `enclosing`.
 */
predicate ofAcquireToLocal(FunctionCall acq, LocalScopeVariable v, Function enclosing) {
  isOfAcquire(acq.getTarget()) and
  enclosing = acq.getEnclosingFunction() and
  exists(AssignExpr ae |
    ae.getRValue() = acq and
    ae.getLValue() = v.getAnAccess()
  )
  or
  isOfAcquire(acq.getTarget()) and
  enclosing = acq.getEnclosingFunction() and
  v.getInitializer().getExpr() = acq
}

/**
 * The control-flow node `n` reaches an exit (return / function end)
 * within `enclosing` without passing through an of_node_put call
 * whose argument refers to `v`.
 */
predicate reachesExitWithoutRelease(
  ControlFlowNode n, LocalScopeVariable v, Function enclosing
) {
  n.getControlFlowScope() = enclosing and
  (
    n instanceof ReturnStmt
    or
    not exists(n.getASuccessor()) and n.getControlFlowScope() = enclosing
  )
  or
  exists(ControlFlowNode succ |
    succ = n.getASuccessor() and
    reachesExitWithoutRelease(succ, v, enclosing) and
    not (
      succ.(FunctionCall).getTarget().getName() = "of_node_put" and
      succ.(FunctionCall).getArgument(0) = v.getAnAccess()
    )
  )
}

/**
 * `ret` is a return statement inside `enclosing` that is reached from
 * `acq` without an intervening of_node_put on `v`.
 */
predicate badReturnAfterAcquire(
  FunctionCall acq, LocalScopeVariable v, Function enclosing, ReturnStmt ret
) {
  ofAcquireToLocal(acq, v, enclosing) and
  ret.getEnclosingFunction() = enclosing and
  exists(ControlFlowNode cur |
    cur = acq.getASuccessor*() and
    cur = ret and
    pathHasNoRelease(acq, ret, v)
  )
}

/**
 * There exists a control-flow path from `acq` to `ret` that does not
 * pass through an of_node_put call whose argument is `v`.
 */
predicate pathHasNoRelease(FunctionCall acq, ReturnStmt ret, LocalScopeVariable v) {
  exists(ControlFlowNode cur |
    cur = acq and
    reachesNodeWithoutRelease(cur, ret, v)
  )
}

predicate reachesNodeWithoutRelease(
  ControlFlowNode src, ControlFlowNode dst, LocalScopeVariable v
) {
  src = dst
  or
  exists(ControlFlowNode succ |
    succ = src.getASuccessor() and
    not (
      succ.(FunctionCall).getTarget().getName() = "of_node_put" and
      succ.(FunctionCall).getArgument(0) = v.getAnAccess()
    ) and
    reachesNodeWithoutRelease(succ, dst, v)
  )
}

from FunctionCall acq, LocalScopeVariable v, Function enclosing, ReturnStmt ret
where
  badReturnAfterAcquire(acq, v, enclosing, ret) and
  // Filter: ensure the function has at least one of_node_put on v somewhere,
  // indicating the developer recognized the resource needs releasing on
  // SOME paths but missed others. This reduces FPs where the node is
  // intentionally returned to the caller.
  exists(FunctionCall rel |
    rel.getEnclosingFunction() = enclosing and
    rel.getTarget().getName() = "of_node_put" and
    rel.getArgument(0) = v.getAnAccess()
  ) and
  // Exclude returns that themselves return the acquired node
  not ret.getExpr() = v.getAnAccess()
select ret,
  "Possible refcount leak: of_node_put on '" + v.getName() +
    "' (acquired by $@) is missing on this return path.", acq, acq.getTarget().getName()
