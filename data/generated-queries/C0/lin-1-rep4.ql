/**
 * @name Missing of_node_put after of_parse_phandle family in loop
 * @description A device_node obtained from of_parse_phandle / of_get_child_by_name /
 *              of_find_node_by_* / of_get_next_child must be released with
 *              of_node_put() on every exit path. In loop bodies, an early
 *              `continue` or `break` that skips the of_node_put() call leaks
 *              the device_node refcount.
 * @kind problem
 * @problem.severity warning
 * @id cpp/of-node-leak-loop-exit
 * @tags correctness
 *       reliability
 *       resource-leak
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph

/**
 * Functions in the of_* family whose returned `struct device_node *` carries
 * an incremented refcount that the caller must release with `of_node_put`.
 */
predicate isOfNodeAcquire(Function f) {
  exists(string n | n = f.getName() |
    n = "of_parse_phandle" or
    n = "of_parse_phandle_with_args" or
    n = "of_parse_phandle_with_fixed_args" or
    n = "of_get_child_by_name" or
    n = "of_get_next_child" or
    n = "of_get_next_available_child" or
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

/** A call that releases a device_node refcount. */
predicate isOfNodePut(FunctionCall c) {
  c.getTarget().getName() = "of_node_put"
}

/** A call that transfers ownership (so caller is no longer responsible). */
predicate transfersOwnership(FunctionCall c) {
  exists(string n | n = c.getTarget().getName() |
    n = "of_node_get" or
    n.matches("of_changeset_%") or
    n.matches("%add_child%") or
    n.matches("%attach_node%")
  )
}

/**
 * Call to an of_* acquire function inside a loop, whose result is stored in
 * a local variable used as the critical resource.
 */
class OfAcquireInLoop extends FunctionCall {
  Variable criticalVar;
  Loop loop;

  OfAcquireInLoop() {
    isOfNodeAcquire(this.getTarget()) and
    this.getEnclosingStmt().getParentStmt*() = loop.getStmt() and
    exists(AssignExpr a |
      a.getRValue() = this and
      a.getLValue() = criticalVar.getAnAccess()
    )
  }

  Variable getCriticalVar() { result = criticalVar }

  Loop getLoop() { result = loop }
}

/**
 * Holds if `s` is a statement inside `loop` that exits the current iteration
 * (continue / break / return / goto out-of-loop) without a preceding
 * of_node_put on `v` along the path from the acquire.
 */
predicate isLeakyExit(Stmt s, Loop loop, Variable v) {
  s.getParentStmt*() = loop.getStmt() and
  (
    s instanceof ContinueStmt or
    s instanceof BreakStmt or
    s instanceof ReturnStmt or
    s instanceof GotoStmt
  ) and
  not exists(FunctionCall put |
    isOfNodePut(put) and
    put.getAnArgument() = v.getAnAccess() and
    put.getEnclosingStmt().getParentStmt*() = loop.getStmt() and
    // put dominates the exit textually within the loop iteration
    put.getLocation().getStartLine() < s.getLocation().getStartLine() and
    put.getEnclosingStmt().getParentStmt*() = s.getParentStmt+()
  )
}

from OfAcquireInLoop acq, Variable v, Loop loop, Stmt exit
where
  v = acq.getCriticalVar() and
  loop = acq.getLoop() and
  exit.getParentStmt*() = loop.getStmt() and
  (
    exit instanceof ContinueStmt or
    exit instanceof BreakStmt
  ) and
  exit.getLocation().getStartLine() > acq.getLocation().getStartLine() and
  // No of_node_put on v between acquire and exit within the same iteration body
  not exists(FunctionCall put |
    isOfNodePut(put) and
    put.getAnArgument() = v.getAnAccess() and
    put.getEnclosingStmt().getParentStmt*() = loop.getStmt() and
    put.getLocation().getStartLine() > acq.getLocation().getStartLine() and
    put.getLocation().getStartLine() < exit.getLocation().getStartLine()
  ) and
  // Exclude cases where ownership is transferred
  not exists(FunctionCall xfer |
    transfersOwnership(xfer) and
    xfer.getAnArgument() = v.getAnAccess() and
    xfer.getEnclosingStmt().getParentStmt*() = loop.getStmt() and
    xfer.getLocation().getStartLine() > acq.getLocation().getStartLine() and
    xfer.getLocation().getStartLine() < exit.getLocation().getStartLine()
  )
select exit,
  "Loop exit (" + exit.toString() + ") may leak device_node '" + v.getName() +
    "' acquired by $@ without of_node_put.", acq, acq.getTarget().getName()
