/**
 * @name Missing error code assignment on failure goto path
 * @description Detects a failure check (e.g. `if (!ptr)`) whose then-branch
 *              jumps via `goto` to a cleanup label that falls through to a
 *              `return errvar;` statement, but the then-branch does NOT
 *              assign a non-zero value to that error variable before the
 *              goto. Callers therefore see success despite the failure.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-err-3
 * @tags correctness
 *       error-handling
 */

import cpp

/**
 * `err` is a function-local int variable initialized to 0 and returned by
 * at least one `return` statement of `f`.
 */
predicate isErrorVar(Function f, LocalVariable err) {
  err.getFunction() = f and
  err.getType().getUnspecifiedType() instanceof IntegralType and
  err.getInitializer().getExpr().getValue() = "0" and
  exists(ReturnStmt ret |
    ret.getEnclosingFunction() = f and
    ret.getExpr().(VariableAccess).getTarget() = err
  )
}

/**
 * A goto statement targeting a label that falls through to a return of
 * the error variable.
 */
predicate gotoToCleanup(GotoStmt gs, LocalVariable err) {
  exists(Function f, LabelStmt lbl, ReturnStmt ret |
    gs.getEnclosingFunction() = f and
    isErrorVar(f, err) and
    gs.getTarget() = lbl and
    ret.getEnclosingFunction() = f and
    ret.getExpr().(VariableAccess).getTarget() = err and
    lbl.getLocation().getStartLine() < ret.getLocation().getStartLine()
  )
}

/** A "failure" if-condition: `!expr`, `expr == 0`, or `expr == NULL`. */
predicate isFailureCheck(IfStmt is) {
  is.getCondition() instanceof NotExpr
  or
  exists(EQExpr eq |
    eq = is.getCondition() and
    (eq.getRightOperand().getValue() = "0" or eq.getLeftOperand().getValue() = "0")
  )
}

from IfStmt is, GotoStmt gs, LocalVariable err
where
  isFailureCheck(is) and
  gotoToCleanup(gs, err) and
  gs.getParentStmt*() = is.getThen() and
  // No assignment to err inside the then branch before the goto
  not exists(Assignment a |
    a.getLValue().(VariableAccess).getTarget() = err and
    a.getEnclosingStmt().getParentStmt*() = is.getThen()
  )
select gs, "goto to cleanup label without assigning error code; function will return 0 ($@) despite failure.", err, err.getName()
