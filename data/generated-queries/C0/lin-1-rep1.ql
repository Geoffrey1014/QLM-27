/**
 * @name Missing of_node_put on device_node from of_parse_phandle family
 * @description A device_node pointer obtained via the of_parse_phandle / of_get_*
 *              family must be released with of_node_put on every path that
 *              leaves the scope (including early continue/break/return).
 *              Missing of_node_put causes a device_node refcount leak.
 * @kind problem
 * @problem.severity warning
 * @id cpp/missing-of-node-put
 * @tags reliability
 *       resource-leak
 *       kernel
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph

/**
 * Names of OF helpers that acquire a `struct device_node *` reference and
 * require a paired `of_node_put` to release it.
 */
predicate ofAcquireName(string n) {
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
  n = "of_find_node_with_property"
}

/** A call to an OF function that returns/produces an owned device_node ref. */
class OfAcquireCall extends FunctionCall {
  OfAcquireCall() { ofAcquireName(this.getTarget().getName()) }
}

/** A call that releases a device_node reference. */
class OfReleaseCall extends FunctionCall {
  OfReleaseCall() {
    this.getTarget().getName() = "of_node_put" or
    // common wrappers that also drop the ref
    this.getTarget().getName() = "of_node_put_kfree"
  }
}

/**
 * Local variable that holds the result of an of_* acquire call.
 * We restrict to local variables to keep the query intraprocedural.
 */
class AcquiredNodeVar extends LocalVariable {
  OfAcquireCall acq;

  AcquiredNodeVar() {
    // either initialised at declaration or assigned later from the acquire call
    (
      this.getInitializer().getExpr() = acq
      or
      exists(AssignExpr a |
        a.getLValue().(VariableAccess).getTarget() = this and
        a.getRValue() = acq
      )
    )
  }

  OfAcquireCall getAcquire() { result = acq }
}

/** Holds if `release` is an of_node_put call whose argument refers to `v`. */
predicate releasesVar(OfReleaseCall release, LocalVariable v) {
  release.getArgument(0).(VariableAccess).getTarget() = v
}

/**
 * Holds if some basic block reachable from `acq` (within the same enclosing
 * function) is an exit-like terminator (continue/break/return/goto out)
 * that leaves the loop iteration WITHOUT first executing of_node_put(v).
 *
 * Approximation: there exists a control-flow path from `acq` to a function
 * exit point (or to a backedge of the enclosing loop) on which no
 * of_node_put(v) call appears.
 */
predicate missingReleaseOnSomePath(OfAcquireCall acq, AcquiredNodeVar v, ControlFlowNode endp) {
  acq = v.getAcquire() and
  acq.getEnclosingFunction() = endp.getControlFlowScope() and
  (
    // path to a return/exit of the function
    endp instanceof ReturnStmt
    or
    // path that leaves the iteration early (continue/break/goto)
    endp instanceof ContinueStmt
    or
    endp instanceof BreakStmt
    or
    endp instanceof GotoStmt
  ) and
  acq.getASuccessor+() = endp and
  not exists(OfReleaseCall rel |
    releasesVar(rel, v) and
    acq.getASuccessor+() = rel and
    rel.getASuccessor*() = endp
  )
}

from OfAcquireCall acq, AcquiredNodeVar v, ControlFlowNode endp, Function f
where
  acq = v.getAcquire() and
  f = acq.getEnclosingFunction() and
  missingReleaseOnSomePath(acq, v, endp) and
  // Exclude functions that never call of_node_put at all on this var anywhere
  // (purely defensive — those are still bugs, keep them).
  exists(endp)
select acq,
  "Device node acquired by $@ may leak: no of_node_put on path to " +
    endp.toString() + " in " + f.getName() + ".",
  acq, acq.getTarget().getName()
