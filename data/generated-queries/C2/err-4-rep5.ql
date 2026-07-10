/**
 * @name  rq3-c2-err-4-rep5
 * @id    cpp/rq3/c2/err-4-rep5
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects goto-to-error-label without assigning a negative
 *              error code to the function's returned status variable.
 */

import cpp

/** Holds if function `f` ends with `return status;` where `status` is a local variable. */
predicate returns_status_var(Function f, LocalVariable status) {
  exists(ReturnStmt ret |
    ret.getEnclosingFunction() = f and
    ret.getExpr().(VariableAccess).getTarget() = status
  ) and
  status.getFunction() = f
}

/** Holds if `labelStmt` is an error-handling label in `f` that leads to a
 *  return of the status variable (i.e., it's the target of cleanup gotos
 *  on the error path). */
predicate is_error_label(Function f, LocalVariable status, Stmt labelStmt) {
  returns_status_var(f, status) and
  labelStmt instanceof LabelStmt and
  labelStmt.getEnclosingFunction() = f and
  // Heuristic: error labels typically have names with "fail", "err", "out", "abort", "cleanup".
  exists(string n | n = labelStmt.(LabelStmt).getName().toLowerCase() |
    n.matches("%fail%") or
    n.matches("%err%") or
    n.matches("%out%") or
    n.matches("%abort%") or
    n.matches("%cleanup%") or
    n.matches("%undo%")
  )
}

/** Holds if `g` is a goto in `f` that jumps to an error label `labelStmt`. */
predicate goto_to_error_label(Function f, LocalVariable status, GotoStmt g, Stmt labelStmt) {
  is_error_label(f, status, labelStmt) and
  g.getEnclosingFunction() = f and
  g.(GotoStmt).getTarget() = labelStmt
}

/** Holds if there exists an assignment to `status` that may reach (textually
 *  precedes within the same enclosing basic block path) the goto `g`.
 *  We check whether any assignment to `status` occurs in the same enclosing
 *  block-statement (or one of its ancestors) that contains `g`, lexically
 *  before `g`. This is a coarse approximation but works without dataflow. */
predicate assigns_status_before_goto(GotoStmt g, LocalVariable status) {
  exists(Assignment a |
    a.getLValue().(VariableAccess).getTarget() = status and
    a.getEnclosingFunction() = g.getEnclosingFunction() and
    (
      // Same parent block, lexically earlier.
      a.getParent+() = g.getParent() and
      a.getLocation().getStartLine() < g.getLocation().getStartLine()
      or
      // Or in an ancestor scope, lexically earlier in the function.
      a.getLocation().getStartLine() < g.getLocation().getStartLine() and
      a.getEnclosingStmt().getParent*() = g.getEnclosingStmt().getParent*()
    )
  )
  or
  // Or status is initialized at declaration with a non-zero value (negative errno) before the goto.
  exists(Expr init |
    status.getInitializer().getExpr() = init and
    init.getValue().toInt() < 0 and
    init.getLocation().getStartLine() < g.getLocation().getStartLine()
  )
}

/** Holds if `g` is the body of a failure check, i.e. it is enclosed by an
 *  `if` whose condition tests a result for failure (negation, comparison
 *  with 0/NULL, or `<0`). */
predicate goto_in_failure_branch(GotoStmt g) {
  exists(IfStmt ifs |
    ifs.getEnclosingFunction() = g.getEnclosingFunction() and
    g.getParent*() = ifs.getThen() and
    (
      // !x
      ifs.getCondition() instanceof NotExpr
      or
      // x < 0 or x <= -1, etc.
      exists(RelationalOperation rel | rel = ifs.getCondition() and rel.getAnOperand().getValue().toInt() <= 0)
      or
      // x == NULL / x == 0
      exists(EQExpr eq | eq = ifs.getCondition() and eq.getAnOperand().getValue().toInt() = 0)
      or
      // unlikely(...) or likely(...) wrapping the above
      exists(FunctionCall fc | fc = ifs.getCondition() and
        (fc.getTarget().getName() = "unlikely" or fc.getTarget().getName() = "likely"))
      or
      // bare variable used as boolean negated check, e.g. if (status) goto fail;
      ifs.getCondition() instanceof VariableAccess
    )
  )
}

/** A goto on a failure branch jumping to an error label, where the status
 *  variable has NOT been assigned to a (negative) error code on this path. */
predicate buggy_goto(Function f, LocalVariable status, GotoStmt g) {
  exists(Stmt labelStmt | goto_to_error_label(f, status, g, labelStmt)) and
  goto_in_failure_branch(g) and
  not assigns_status_before_goto(g, status)
}

from Function f, LocalVariable status, GotoStmt g
where buggy_goto(f, status, g)
select g,
  "Goto to error-return label without assigning error code to status variable '" +
    status.getName() + "' in function '" + f.getName() + "'."
