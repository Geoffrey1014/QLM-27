/**
 * @name Missing error code on failure goto path
 * @description Detects functions returning an int error code that contain a
 *              failure check (`if (!resource)` or similar negative test)
 *              whose body jumps via `goto` to a cleanup label, but does NOT
 *              assign the error variable before jumping. The function then
 *              returns the still-zero error variable, so callers see
 *              success despite the failure.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-err-4
 * @tags correctness
 *       error-handling
 */

import cpp

/**
 * The local "error" variable of a function: an int (or signed integral)
 * local that is initialized to 0 at declaration and is the variable used
 * in the function's return statement.
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
 * `gs` is a GotoStmt that targets a cleanup label `lbl` whose block
 * contains a return of the error variable.
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

/**
 * An IfStmt whose condition is a "negative/failure" test, e.g. `if (!x)`
 * or `if (x == NULL)` or `if (x == 0)`.
 */
predicate isFailureCheck(IfStmt is) {
  is.getCondition() instanceof NotExpr
  or
  exists(EQExpr eq |
    eq = is.getCondition() and
    (eq.getRightOperand().getValue() = "0" or eq.getLeftOperand().getValue() = "0")
  )
}

/**
 * `gs` is a goto inside the `then` branch of a failure-check `if`, and
 * the then branch does not assign the error variable `err` before the
 * goto fires.
 */
predicate failureGotoMissesErrAssign(IfStmt is, GotoStmt gs, LocalVariable err) {
  isFailureCheck(is) and
  gotoToCleanup(gs, err) and
  gs.getParentStmt*() = is.getThen() and
  not exists(Assignment a |
    a.getLValue().(VariableAccess).getTarget() = err and
    a.getEnclosingStmt().getParentStmt*() = is.getThen()
  )
}

from Function f, IfStmt is, GotoStmt gs, LocalVariable err
where
  isErrorVar(f, err) and
  is.getEnclosingFunction() = f and
  failureGotoMissesErrAssign(is, gs, err) and
  exists(Assignment a2 |
    a2.getEnclosingFunction() = f and
    a2.getLValue().(VariableAccess).getTarget() = err
  )
select is, "Failure check jumps to cleanup label without assigning error code; function will return success ($@) on this failure path.", err, err.getName()
