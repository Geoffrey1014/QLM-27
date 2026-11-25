/**
 * @name Missing of_node_put on early exit from for_each_child loop
 * @description Detects cases where a for_each_available_child_of_node (or similar) loop
 *              is exited early via goto/break/return without calling of_node_put() on
 *              the loop variable. This causes a reference count leak.
 *              Pattern from Linux commit 9a2ea132df860177b33c9fd421b26c4e9a0a9396.
 * @kind problem
 * @problem.severity warning
 * @precision high
 * @id cpp/missing-refcount-release-loop
 * @tags reliability
 *       security
 *       external/cwe/cwe-911
 */

import cpp

/**
 * A call to of_get_next_available_child or similar functions that acquire a refcount.
 * These functions increment the reference count on the returned node.
 */
class RefcountAcquireCall extends FunctionCall {
  RefcountAcquireCall() {
    this.getTarget().hasName([
      "of_get_next_available_child",
      "of_get_next_child",
      "of_get_next_child_with_prefix",
      "of_get_next_status_child"
    ])
  }
}

/**
 * A call to of_node_put that releases a reference.
 */
class RefcountReleaseCall extends FunctionCall {
  RefcountReleaseCall() {
    this.getTarget().hasName("of_node_put")
  }
}

/**
 * A for loop that iterates using a refcount-acquiring function.
 * This matches for_each_available_child_of_node and similar macros.
 */
class RefcountIteratorLoop extends ForStmt {
  Variable loopVar;

  RefcountIteratorLoop() {
    // The loop condition or update involves a refcount-acquiring call
    exists(RefcountAcquireCall acquireCall |
      acquireCall.getParent*() = this.getCondition() or
      acquireCall.getParent*() = this.getUpdate() or
      acquireCall.getParent*() = this.getInitialization()
    ) and
    // Identify the loop variable (typically the child node pointer)
    exists(Variable v, VariableAccess va |
      va.getParent*() = this.getCondition() and
      va.getTarget() = v and
      v.getType() instanceof PointerType and
      loopVar = v
    )
  }

  Variable getLoopVariable() { result = loopVar }
}

/**
 * A goto statement inside a loop that exits the loop (target label is outside the loop).
 */
class GotoExitingLoop extends GotoStmt {
  RefcountIteratorLoop loop;

  GotoExitingLoop() {
    loop.getStmt().getAChild*() = this and
    // The target label is outside the loop
    not loop.getStmt().getAChild*() = this.getTarget()
  }

  RefcountIteratorLoop getLoop() { result = loop }

  LabelStmt getTargetLabel() { result = this.getTarget() }
}

/**
 * Checks if there's a refcount release call for the given variable
 * immediately before the given goto statement (in the same if-block).
 */
predicate hasReleaseBeforeGoto(Variable v, GotoStmt gotoStmt) {
  exists(RefcountReleaseCall releaseCall, IfStmt ifStmt |
    releaseCall.getAnArgument().(VariableAccess).getTarget() = v and
    // Both are in the same if-then block
    ifStmt.getThen().getAChild*() = releaseCall and
    ifStmt.getThen().getAChild*() = gotoStmt and
    // Release comes before goto
    releaseCall.getLocation().getStartLine() < gotoStmt.getLocation().getStartLine()
  )
}

/**
 * Find goto statements that exit refcount iterator loops without releasing.
 */
from RefcountIteratorLoop loop, GotoExitingLoop gotoStmt, Variable loopVar, LabelStmt targetLabel
where
  gotoStmt.getLoop() = loop and
  loopVar = loop.getLoopVariable() and
  targetLabel = gotoStmt.getTargetLabel() and
  not hasReleaseBeforeGoto(loopVar, gotoStmt)
select gotoStmt,
  "Potential refcount leak: 'goto " + targetLabel.getName() +
  "' exits the for_each_*_child_of_node loop without calling of_node_put() on loop variable '" +
  loopVar.getName() + "'."
