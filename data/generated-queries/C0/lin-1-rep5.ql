/**
 * @name Missing of_node_put on device_node reference acquired from of_* API
 * @description A device_node pointer obtained from an of_* node-acquiring API
 *              (of_parse_phandle, of_get_child_by_name, of_get_next_child,
 *              of_find_node_by_name, of_get_cpu_node, etc.) must be released
 *              with of_node_put on every path that does not transfer ownership.
 *              Missing of_node_put on continue/break/early-return paths causes
 *              device_node reference leaks.
 * @kind problem
 * @problem.severity warning
 * @id cpp/missing-of-node-put
 * @tags reliability
 *       correctness
 *       resource-leak
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph

/**
 * Functions in the of_* family that acquire (take a refcount on) a
 * `struct device_node *` that the caller must release with of_node_put.
 */
predicate isOfNodeAcquireFunc(Function f) {
  exists(string n | n = f.getName() |
    n = "of_parse_phandle" or
    n = "of_parse_phandle_with_args" or
    n = "of_parse_phandle_with_fixed_args" or
    n = "of_get_child_by_name" or
    n = "of_get_next_child" or
    n = "of_get_next_available_child" or
    n = "of_get_next_cpu_node" or
    n = "of_get_compatible_child" or
    n = "of_get_parent" or
    n = "of_get_next_parent" or
    n = "of_find_node_by_name" or
    n = "of_find_node_by_path" or
    n = "of_find_node_by_phandle" or
    n = "of_find_node_by_type" or
    n = "of_find_compatible_node" or
    n = "of_find_matching_node" or
    n = "of_find_matching_node_and_match" or
    n = "of_find_node_with_property" or
    n = "of_get_cpu_node" or
    n = "of_cpu_device_node_get"
  )
}

/** A call to an of_* acquire function whose returned node-ref must be released. */
class OfAcquireCall extends FunctionCall {
  OfAcquireCall() { isOfNodeAcquireFunc(this.getTarget()) }
}

/** A call to of_node_put (the release operation). */
class OfNodePutCall extends FunctionCall {
  OfNodePutCall() { this.getTarget().getName() = "of_node_put" }
}

/**
 * Holds if `v` is assigned the result of an of_* acquire call inside `loop`.
 */
predicate acquiresInLoop(Loop loop, LocalVariable v, OfAcquireCall acq) {
  acq.getEnclosingStmt().getParentStmt*() = loop.getStmt() and
  exists(Assignment a |
    a.getEnclosingStmt().getParentStmt*() = loop.getStmt() and
    a.getLValue() = v.getAnAccess() and
    a.getRValue() = acq
  )
}

/**
 * Holds if statement `s` inside `loop` exits the current iteration (continue)
 * or the loop (break/return/goto) without calling of_node_put on `v`.
 */
predicate exitsIterationWithoutPut(Loop loop, LocalVariable v, Stmt exitStmt) {
  exitStmt.getParentStmt*() = loop.getStmt() and
  (
    exitStmt instanceof ContinueStmt or
    exitStmt instanceof BreakStmt or
    exitStmt instanceof ReturnStmt or
    exitStmt instanceof GotoStmt
  ) and
  // The basic block leading to the exit does not call of_node_put on v.
  not exists(OfNodePutCall put |
    put.getEnclosingStmt().getParentStmt*() = loop.getStmt() and
    put.getArgument(0) = v.getAnAccess() and
    put.getEnclosingStmt().(ControlFlowNode).getASuccessor*() =
      exitStmt.(ControlFlowNode)
  )
}

from Loop loop, LocalVariable v, OfAcquireCall acq, Stmt exitStmt
where
  acquiresInLoop(loop, v, acq) and
  exitsIterationWithoutPut(loop, v, exitStmt) and
  // The loop body contains a successful path that DOES call of_node_put on v;
  // this filters loops where the node-ref is intentionally returned to caller.
  exists(OfNodePutCall put |
    put.getEnclosingStmt().getParentStmt*() = loop.getStmt() and
    put.getArgument(0) = v.getAnAccess()
  ) and
  // Ensure the exit precedes the put on at least one path (i.e. early-out leak).
  not exitStmt.(ControlFlowNode).getASuccessor*() =
    any(OfNodePutCall put2 |
      put2.getEnclosingStmt().getParentStmt*() = loop.getStmt() and
      put2.getArgument(0) = v.getAnAccess()
    ).(ControlFlowNode)
select exitStmt,
  "Possible device_node reference leak: '" + v.getName() +
    "' acquired from $@ may not be released by of_node_put before this " +
    exitStmt.toString() + ".", acq, acq.getTarget().getName()
