/**
 * @name  rq3-c2-lin-2-rep5
 * @id    cpp/rq3/c2/lin-2-rep5
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects of_node refcount leaks caused by goto/return/break inside a
 *              for_each_available_child_of_node-style loop that bypasses
 *              of_node_put(child) on the iterator variable.
 */

import cpp

/**
 * The variable `child` is a `struct device_node *` that serves as the iterator
 * of a `for_each_available_child_of_node` / `for_each_child_of_node` macro.
 * After macro expansion these become a ForStmt whose body calls
 * `of_get_next_available_child` or `of_get_next_child` (the underlying
 * iterator helper that bumps the refcount).
 */
predicate iter_child_variable(ForStmt loop, Variable child) {
  child.getType().getUnspecifiedType().(PointerType).getBaseType().getName() =
    "device_node" and
  exists(FunctionCall iter |
    iter.getEnclosingStmt().getParentStmt*() = loop and
    iter.getTarget().getName() =
      ["of_get_next_available_child", "of_get_next_child"] and
    iter.getAnArgument() = child.getAnAccess()
  )
}

/**
 * `s` is a statement lexically inside `loop`'s body that breaks out of the
 * normal next-iteration sequencing: return, break, or goto-to-a-label-outside.
 */
predicate exits_loop_early(ForStmt loop, Stmt s) {
  s.getParentStmt+() = loop.getStmt() and
  (
    s instanceof ReturnStmt
    or
    s instanceof BreakStmt
    or
    exists(GotoStmt g | g = s and not g.getTarget().getParentStmt*() = loop.getStmt())
  )
}

/**
 * A call to of_node_put(child) anywhere lexically before `before` in the same
 * enclosing function. Approximation of "release happens on the path to exit".
 */
predicate puts_child_before(Variable child, Stmt before) {
  exists(FunctionCall put |
    put.getTarget().getName() = "of_node_put" and
    put.getAnArgument() = child.getAnAccess() and
    put.getEnclosingFunction() = before.getEnclosingFunction() and
    put.getLocation().getStartLine() < before.getLocation().getStartLine()
  )
}

/**
 * Composed predicate: the early-exit statement leaks the iterator refcount
 * because no of_node_put(child) precedes it within the loop body.
 */
predicate leaks_iterator_refcount(ForStmt loop, Variable child, Stmt exitStmt) {
  iter_child_variable(loop, child) and
  exits_loop_early(loop, exitStmt) and
  not puts_child_before(child, exitStmt)
}

from ForStmt loop, Variable child, Stmt exitStmt
where leaks_iterator_refcount(loop, child, exitStmt)
select exitStmt,
  "Early exit from for_each_available_child_of_node loop without of_node_put($@).",
  child, child.getName()
