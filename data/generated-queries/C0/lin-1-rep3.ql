/**
 * @name Missing of_node_put on device_node acquired via of_* family
 * @description A device_node obtained from of_parse_phandle (and similar
 *              acquiring helpers in the of_* family) must be released with
 *              of_node_put on every path that exits the variable's scope,
 *              including early continue/break/return on error or skip
 *              conditions. Missing the release leaks a refcount on the node.
 * @kind problem
 * @problem.severity warning
 * @id cpp/of-node-ref-leak
 * @tags correctness
 *       reliability
 *       memory-leak
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph

/**
 * Functions that acquire (take a reference on) a device_node and return it.
 * Includes the of_parse_phandle family plus other common acquirers whose
 * returned pointer must be balanced with of_node_put.
 */
predicate isOfNodeAcquire(Function f) {
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
      "of_node_get"
    ]
}

/** A call that releases a device_node reference. */
predicate isOfNodeRelease(FunctionCall c, Expr arg) {
  c.getTarget().getName() = "of_node_put" and
  arg = c.getArgument(0)
}

/**
 * Holds if `v` is assigned the result of an of_* acquire call at `acq`.
 */
predicate acquiredInto(LocalVariable v, FunctionCall acq) {
  isOfNodeAcquire(acq.getTarget()) and
  (
    // direct initializer:  struct device_node *v = of_parse_phandle(...);
    v.getInitializer().getExpr() = acq
    or
    // subsequent assignment: v = of_parse_phandle(...);
    exists(AssignExpr ae |
      ae.getRValue() = acq and
      ae.getLValue().(VariableAccess).getTarget() = v
    )
  )
}

/**
 * Holds if `n` is a control-flow node at which `v` is known to currently
 * hold an acquired (live) device_node reference: i.e. there is a CFG path
 * from the acquire `acq` to `n` that does not pass through an of_node_put
 * on `v` and does not reassign `v`.
 */
predicate liveAcquired(LocalVariable v, FunctionCall acq, ControlFlowNode n) {
  acquiredInto(v, acq) and
  n = acq
  or
  exists(ControlFlowNode prev |
    liveAcquired(v, acq, prev) and
    n = prev.getASuccessor() and
    // not released on this step
    not exists(FunctionCall rel, Expr arg |
      isOfNodeRelease(rel, arg) and
      arg.(VariableAccess).getTarget() = v and
      rel = n
    ) and
    // not reassigned on this step
    not exists(AssignExpr ae |
      ae = n and
      ae.getLValue().(VariableAccess).getTarget() = v
    )
  )
}

/**
 * A `continue`, `break`, or `return` statement at which `v` is still
 * holding an acquired device_node reference.
 */
predicate leakingExit(LocalVariable v, FunctionCall acq, Stmt exit) {
  liveAcquired(v, acq, exit) and
  (
    exit instanceof ContinueStmt or
    exit instanceof BreakStmt or
    exit instanceof ReturnStmt
  ) and
  // and there is no of_node_put(v) statically dominating this exit within
  // the same enclosing loop iteration / function epoch (approximated by
  // requiring that NO release of v exists between acq and exit on this path,
  // which liveAcquired already enforces).
  acq.getEnclosingFunction() = exit.getEnclosingFunction()
}

from LocalVariable v, FunctionCall acq, Stmt exit, Function enclosing
where
  leakingExit(v, acq, exit) and
  enclosing = acq.getEnclosingFunction() and
  // suppress trivial false positives: the variable must actually have type
  // pointer-to-something (we don't try to match struct device_node by name
  // because typedef chains and forward decls vary).
  v.getType().getUnderlyingType() instanceof PointerType
select exit,
  "Possible of_node refcount leak: '" + v.getName() +
    "' acquired by $@ is not released by of_node_put before this " +
    exit.getAPrimaryQlClass() + " exits its scope.",
  acq, acq.getTarget().getName()
