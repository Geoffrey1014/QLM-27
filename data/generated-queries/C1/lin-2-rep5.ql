/**
 * @name Missing of_node_put on early exit from for_each_available_child_of_node
 * @description Detects loops over device-tree child nodes (via
 *   for_each_available_child_of_node or similar of_get_next_*_child iteration
 *   macros) that break out of the loop body via an early `goto`, `return`,
 *   or `break` without calling `of_node_put` on the loop's iterator node,
 *   which leaks a refcount on the device_node.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-lin-2
 * @tags correctness reliability resource-leak
 */

import cpp

/** A call whose target advances to the next OF child node, returning a
 *  refcounted `struct device_node *` that the caller must release. */
predicate isOfNextChildCall(FunctionCall fc) {
  exists(string n | n = fc.getTarget().getName() |
    n = "of_get_next_available_child" or
    n = "of_get_next_child" or
    n = "of_get_next_cpu_node"
  )
}

/** A for-loop whose update step calls an of_get_next_*_child iterator and
 *  assigns the result to variable `v` (the loop iterator). */
predicate ofChildLoop(ForStmt loop, Variable v) {
  exists(FunctionCall fc, Assignment a |
    isOfNextChildCall(fc) and
    fc.getParent*() = loop.getUpdate() and
    a.getParent*() = loop.getUpdate() and
    a.getLValue() = v.getAnAccess() and
    a.getRValue().getAChild*() = fc
  )
}

/** A call `of_node_put(v)` applied to variable `v`. */
predicate isOfNodePutOn(FunctionCall fc, Variable v) {
  fc.getTarget().getName() = "of_node_put" and
  fc.getArgument(0) = v.getAnAccess()
}

/** A statement that exits the enclosing function or breaks out of the loop. */
class EarlyExitStmt extends Stmt {
  EarlyExitStmt() {
    this instanceof ReturnStmt or
    this instanceof GotoStmt or
    this instanceof BreakStmt
  }
}

/** True if some of_node_put(v) call statement is a sibling-before of `exit`
 *  in any enclosing block on the way up from `exit` to `loop`. */
predicate releasedBefore(EarlyExitStmt exit, Variable v, ForStmt loop) {
  exists(FunctionCall fc, BlockStmt b, int iExit, int iRel, Stmt sExit, Stmt sRel |
    isOfNodePutOn(fc, v) and
    fc.getEnclosingFunction() = exit.getEnclosingFunction() and
    sExit = exit and
    sRel = fc.getEnclosingStmt() and
    // walk up exit's parent chain to find an ancestor that is a direct child
    // of `b`
    (sExit.getParent*() = b.getAChild() or sExit = b.getAChild()) and
    (sRel.getParent*() = b.getAChild() or sRel = b.getAChild()) and
    b.getIndexOfStmt(getAncestorInBlock(sExit, b)) = iExit and
    b.getIndexOfStmt(getAncestorInBlock(sRel, b)) = iRel and
    iRel < iExit and
    b.getParent*() = loop.getStmt()
  )
}

/** Helper: walks up the parent chain of `s` until reaching a direct child
 *  of block `b`. */
Stmt getAncestorInBlock(Stmt s, BlockStmt b) {
  (result = s or result = s.getParent+()) and
  result = b.getAChild()
}

from ForStmt loop, Variable child, EarlyExitStmt exit
where
  ofChildLoop(loop, child) and
  // exit lives inside the loop body
  exit.getParent+() = loop.getStmt() and
  // and is NOT preceded in an enclosing block by an of_node_put(child)
  not releasedBefore(exit, child, loop)
select exit,
  "Early exit from for_each_available_child_of_node loop without of_node_put(" +
    child.getName() + ") -- leaks device_node refcount."
