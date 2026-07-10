/**
 * @name  rq3-c2-lin-2-rep1
 * @id    cpp/rq3/c2/lin-2-rep1
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects refcount leaks where early-exit (goto/return/break) from a
 *              for_each_available_child_of_node-style loop bypasses of_node_put on
 *              the iteration child node.
 */

import cpp

/**
 * Identifies a `for` loop that originates from a `for_each_available_child_of_node`
 * (or sibling) iterator macro. After macro expansion the loop body refers to the
 * iterator variable (`child`). We recognize such loops by looking for a ForStmt
 * whose condition or init mentions `of_get_next_available_child` /
 * `of_get_next_child` (the underlying iterator), and whose loop variable is the
 * device_node pointer.
 */
predicate is_for_each_child_loop(ForStmt loop, Variable child) {
  exists(FunctionCall fc |
    fc.getEnclosingStmt().getParentStmt*() = loop and
    (
      fc.getTarget().getName() = "of_get_next_available_child" or
      fc.getTarget().getName() = "of_get_next_child"
    )
  ) and
  child.getAnAccess().getEnclosingStmt().getParentStmt*() = loop and
  child.getType().getUnspecifiedType().(PointerType).getBaseType().getName() = "device_node"
}

/**
 * A call that releases (puts) a device_node `child`.
 */
predicate releases_child(FunctionCall rel, Variable child) {
  rel.getTarget().getName() = "of_node_put" and
  rel.getArgument(0) = child.getAnAccess()
}

/**
 * A statement inside the loop body that exits the current iteration / function
 * without continuing the loop normally: `return`, `goto`, or `break`.
 */
predicate early_exit_stmt(ForStmt loop, Stmt exitStmt) {
  exitStmt.getParentStmt*() = loop.getStmt() and
  (
    exitStmt instanceof ReturnStmt or
    exitStmt instanceof GotoStmt or
    exitStmt instanceof BreakStmt
  )
}

/**
 * The exit statement is reachable in the loop body without a preceding
 * of_node_put(child) on the same basic-block-local path.  We approximate
 * "no release before exit" by: the exitStmt's enclosing compound block (or
 * any ancestor compound up to the loop body) contains no `releases_child`
 * call that lexically precedes the exit statement.
 */
predicate leak_at_exit(ForStmt loop, Variable child, Stmt exitStmt) {
  is_for_each_child_loop(loop, child) and
  early_exit_stmt(loop, exitStmt) and
  not exists(FunctionCall rel |
    releases_child(rel, child) and
    rel.getEnclosingStmt().getParentStmt*() = loop.getStmt() and
    rel.getLocation().getStartLine() < exitStmt.getLocation().getStartLine() and
    rel.getEnclosingFunction() = exitStmt.getEnclosingFunction()
  )
}

from ForStmt loop, Variable child, Stmt exitStmt
where leak_at_exit(loop, child, exitStmt)
select exitStmt,
  "Possible of_node refcount leak: early exit from for_each_available_child_of_node loop iterating $@ without of_node_put",
  child, child.getName()
