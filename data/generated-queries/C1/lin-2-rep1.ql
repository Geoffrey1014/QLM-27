/**
 * @name Missing of_node_put on early exit from for_each_*_child_of_node loop
 * @description The Linux for_each_*_child_of_node() family of iterators
 *              acquires a reference (via of_get_next_*_child) on each loop
 *              variable. When a loop body exits early (via break, goto, or
 *              return) the current child node's reference must be released
 *              with of_node_put(), otherwise the device-tree node leaks
 *              (CWE-401).
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-lin-2
 */

import cpp

/* APIs that, when used as the iterator step in a for-loop, acquire a
 * struct device_node* reference that must be released. */
predicate isChildIteratorAcquire(string name) {
  name = "of_get_next_available_child" or
  name = "of_get_next_child" or
  name = "of_get_next_cpu_node" or
  name = "of_get_next_parent" or
  name = "of_get_compatible_child" or
  name = "of_get_child_by_name"
}

predicate isOfReleaseCall(FunctionCall c) {
  c.getTarget().getName() = "of_node_put"
}

/* A for-loop whose update expression calls one of the child-iterator
 * acquire APIs and writes its result into `iterVar`. This matches the
 * expansion of `for_each_*_child_of_node(parent, child)`. */
predicate isChildIterLoop(ForStmt loop, Variable iterVar) {
  exists(FunctionCall step |
    step.getParent*() = loop.getUpdate() and
    isChildIteratorAcquire(step.getTarget().getName()) and
    (
      exists(AssignExpr a |
        a.getParent*() = loop.getUpdate() and
        a.getRValue() = step and
        a.getLValue().(VariableAccess).getTarget() = iterVar
      )
    )
  )
}

/* A statement that exits the loop body without going through the normal
 * loop step (which would call of_node_put on the previous child for us):
 *   - break out of the for-loop
 *   - goto a label outside the loop
 *   - return from the enclosing function
 */
predicate isEarlyExitStmt(Stmt s, ForStmt loop) {
  (
    s instanceof BreakStmt and s.getParent*() = loop.getStmt()
  )
  or
  (
    s instanceof ReturnStmt and s.getParent*() = loop.getStmt()
  )
  or
  exists(GotoStmt g |
    g = s and
    g.getParent*() = loop.getStmt() and
    not g.getTarget().getParent*() = loop.getStmt()
  )
}

/* True if `s` is preceded (in the same basic-block-ish straight-line
 * sequence inside the loop) by an of_node_put call whose argument reads
 * `iterVar`. We approximate by checking that some of_node_put(iterVar)
 * appears in the same enclosing block (or an ancestor block up to the
 * loop body) that lexically precedes `s`. */
predicate hasReleaseBefore(Stmt s, Variable iterVar, ForStmt loop) {
  exists(ExprStmt es, FunctionCall put, VariableAccess va, BlockStmt b |
    isOfReleaseCall(put) and
    es.getExpr() = put and
    va = put.getArgument(0) and
    va.getTarget() = iterVar and
    b.getAStmt() = es and
    b.getAStmt() = s and
    es.getParent*() = loop.getStmt() and
    es.getLocation().getStartLine() < s.getLocation().getStartLine()
  )
}

from ForStmt loop, Variable iterVar, Stmt exitStmt, Function f
where
  isChildIterLoop(loop, iterVar) and
  isEarlyExitStmt(exitStmt, loop) and
  f = loop.getEnclosingFunction() and
  not hasReleaseBefore(exitStmt, iterVar, loop)
select exitStmt,
  "Early loop exit (" + exitStmt.toString() +
    ") inside for_each_*_child_of_node iteration over '" + iterVar.getName() +
    "' without an of_node_put() — leaks the acquired device-tree node reference."
