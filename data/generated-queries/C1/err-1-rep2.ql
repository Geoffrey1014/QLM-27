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
 * @id qlm/c1-err-1
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
  // initializer is the integer literal 0
  err.getInitializer().getExpr().getValue() = "0" and
  // function returns it
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
    // label appears before the return (i.e. cleanup label that falls through to return)
    lbl.getLocation().getStartLine() < ret.getLocation().getStartLine()
  )
}

/**
 * An IfStmt whose condition is a "negative/failure" test of some sub-expr,
 * e.g. `if (!x)` or `if (x == NULL)` or `if (err)`.
 */
predicate isFailureCheck(IfStmt is) {
  // !expr
  is.getCondition() instanceof NotExpr
  or
  // expr == 0 / NULL
  exists(EQExpr eq |
    eq = is.getCondition() and
    (eq.getRightOperand().getValue() = "0" or eq.getLeftOperand().getValue() = "0")
  )
}

/**
 * `gs` is a goto inside the `then` branch of a failure-check `if`, and
 * neither the if-condition's enclosing block nor the if's then branch
 * assigns the error variable `err` before the goto fires.
 */
predicate failureGotoMissesErrAssign(IfStmt is, GotoStmt gs, LocalVariable err) {
  isFailureCheck(is) and
  gotoToCleanup(gs, err) and
  gs.getParentStmt*() = is.getThen() and
  // No assignment to err inside the then branch before the goto
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
  // and the goto is the first/only statement in the then branch (a bare `goto out;`)
  // -- not strictly required; allowed if no err assignment precedes goto.
  // exclude trivial single-return functions: require there is some "success" path
  // that assigns err (so 0 is clearly the wrong returned value here)
  exists(Assignment a2 |
    a2.getEnclosingFunction() = f and
    a2.getLValue().(VariableAccess).getTarget() = err
  )
select is, "Failure check jumps to cleanup label without assigning error code; function will return success ($@) on this failure path.", err, err.getName()
