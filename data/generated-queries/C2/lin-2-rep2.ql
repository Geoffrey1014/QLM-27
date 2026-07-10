/**
 * @name  rq3-c2-lin-2-rep2
 * @id    cpp/rq3/c2/lin-2-rep2
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2 — device_node refcount leak from for_each_available_child_of_node iterator on early exit paths.
 */
import cpp

/* A for-loop produced by the for_each_available_child_of_node iterator macro:
 * the loop's update expression calls of_get_next_available_child(...) and
 * stores the result into the iteration variable `child`. */
predicate iter_macro_loop(ForStmt loop, Variable child) {
  exists(FunctionCall fc |
    fc.getEnclosingStmt().getParentStmt*() = loop and
    fc.getTarget().getName() = "of_get_next_available_child" and
    (
      exists(AssignExpr a | a.getRValue() = fc and a.getLValue() = child.getAnAccess())
      or
      child.getInitializer().getExpr() = fc
    )
  )
}

/* An "early exit" statement lexically inside the loop body that terminates
 * the iteration without going through the macro's normal loop step
 * (break / goto out of the loop / return). */
predicate early_exit_in_loop(ForStmt loop, Stmt exit) {
  exit.getParentStmt+() = loop.getStmt() and
  (
    exit instanceof BreakStmt
    or
    exit instanceof ReturnStmt
    or
    exit instanceof GotoStmt
  )
}

/* True if there is a call to of_node_put(child) lexically before `exit`
 * in the same enclosing function, on a line between the loop start and
 * the exit statement. */
predicate puts_child_before(Variable child, Stmt exit) {
  exists(FunctionCall put |
    put.getTarget().getName() = "of_node_put" and
    put.getArgument(0) = child.getAnAccess() and
    put.getEnclosingFunction() = exit.getEnclosingFunction() and
    put.getLocation().getStartLine() <= exit.getLocation().getStartLine()
  )
}

/* A leak site: an early exit from an iter-macro loop without of_node_put on
 * the iteration variable on that exit path. */
predicate leak_site(ForStmt loop, Variable child, Stmt exit) {
  iter_macro_loop(loop, child) and
  early_exit_in_loop(loop, exit) and
  not puts_child_before(child, exit)
}

from ForStmt loop, Variable child, Stmt exit
where leak_site(loop, child, exit)
select exit, "early exit from for_each_available_child_of_node loop without of_node_put($@)", child, child.getName()
