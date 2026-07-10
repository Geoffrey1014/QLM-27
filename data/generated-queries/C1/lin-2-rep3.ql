/**
 * @name Missing of_node_put on early loop exit
 * @description A loop iterates over device-tree children via an
 *              of_get_next_*-style acquire API (or the equivalent
 *              for_each_*_child_of_node iterator macro). Each iteration
 *              owns a struct device_node* reference that must be released
 *              with of_node_put() before any early exit out of the loop
 *              body (goto / return / break to a label outside the loop).
 *              If such an exit path is reachable without an intervening
 *              of_node_put() on the iterator variable, the device_node
 *              reference leaks (CWE-401 family).
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-lin-2
 */

import cpp

/* Acquire APIs that return a struct device_node* with the refcount
 * incremented by one. The kernel iterator macros
 * (for_each_*_child_of_node, for_each_*_of_node, ...) expand into a
 * for-loop whose step calls one of these. */
predicate isOfChildAcquireApi(string name) {
  name = "of_get_next_child" or
  name = "of_get_next_available_child" or
  name = "of_get_next_cpu_node" or
  name = "of_get_next_parent" or
  name = "of_get_compatible_child" or
  name = "of_get_child_by_name" or
  name = "of_find_node_by_path" or
  name = "of_find_node_opts_by_path" or
  name = "of_find_matching_node" or
  name = "of_find_matching_node_and_match" or
  name = "of_find_compatible_node" or
  name = "of_parse_phandle"
}

predicate isOfNodePut(FunctionCall c) {
  c.getTarget().getName() = "of_node_put"
}

/* The Variable that receives `call`'s return value, either via
 * initialization or assignment. */
Variable getReceiverVariable(FunctionCall call) {
  exists(Variable v |
    v.getInitializer().getExpr() = call and result = v
  )
  or
  exists(AssignExpr a |
    a.getRValue() = call and
    result = a.getLValue().(VariableAccess).getTarget()
  )
}

/* True if `s` is a structural descendant of `outer`. */
predicate stmtInside(Stmt s, Stmt outer) {
  s = outer
  or
  stmtInside(s.getParent(), outer)
}

/* True if `e` is associated with `outer` -- either inside its body
 * statement or appearing as part of the loop's own header (condition/
 * update/init), in which case its enclosing statement IS the loop. */
predicate exprInLoop(Expr e, Loop loop) {
  stmtInside(e.getEnclosingStmt(), loop.getStmt())
  or
  e.getEnclosingStmt() = loop
  or
  /* `for` initializer / `for` update lives directly under the for-stmt */
  e.getParent+() = loop
}

/* The early-exit kinds we care about: a `goto` whose target label is
 * outside the loop, or a `return` inside the loop body. We model
 * `break` similarly via JumpStmt though it is rarer here. */
predicate isEarlyExitFromLoop(Stmt exit, Loop loop) {
  stmtInside(exit, loop.getStmt()) and
  (
    exit instanceof ReturnStmt
    or
    exists(GotoStmt g | g = exit |
      not stmtInside(g.getTarget(), loop.getStmt())
    )
  )
}

/* True if some call of_node_put(v) appears lexically within the loop
 * body strictly before `exit` in the same enclosing basic block / if
 * branch. Approximation: any of_node_put(v) inside the same loop body
 * that is an ancestor-statement-sibling preceding `exit`. We use a
 * conservative check: there exists an of_node_put(v) inside the loop
 * body whose enclosing statement chain shares a parent with `exit`
 * and appears earlier. */
predicate releasedBeforeExit(Variable v, Stmt exit, Loop loop) {
  exists(FunctionCall put, VariableAccess arg, Stmt putStmt |
    isOfNodePut(put) and
    arg = put.getArgument(0) and
    arg.getTarget() = v and
    putStmt = put.getEnclosingStmt() and
    stmtInside(putStmt, loop.getStmt()) and
    /* same enclosing block as exit, and put precedes exit */
    exists(BlockStmt b, int ip, int ie |
      b.getStmt(ip) = putStmt.getParent*() and
      b.getStmt(ie) = exit.getParent*() and
      ip < ie
    )
  )
}

from
  Loop loop, FunctionCall acquire, Variable v, Function f, Stmt exit
where
  /* the loop's iterator is an of_* acquire whose result is stored in v */
  isOfChildAcquireApi(acquire.getTarget().getName()) and
  v = getReceiverVariable(acquire) and
  f = loop.getEnclosingFunction() and
  acquire.getEnclosingFunction() = f and
  exprInLoop(acquire, loop) and
  /* an early-exit path inside the loop */
  isEarlyExitFromLoop(exit, loop) and
  exit.getEnclosingFunction() = f and
  /* no of_node_put(v) appears earlier in the same enclosing block */
  not releasedBeforeExit(v, exit, loop)
select exit,
  "Early exit out of loop iterating over " + acquire.getTarget().getName() +
    " leaves the device_node held by '" + v.getName() +
    "' without an of_node_put() -- reference leak."
