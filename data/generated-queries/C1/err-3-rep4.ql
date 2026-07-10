/**
 * @name Missing error code on failure goto path
 * @description Detects functions returning an int error code where a failure
 *              check (`if (!x)` / `if (x == NULL)`) jumps via goto to a cleanup
 *              label without assigning the error variable, so the function
 *              returns success (0) despite the failure.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-err-3
 * @tags correctness
 *       error-handling
 */

import cpp

/**
 * `err` is a local variable of `f` initialised to 0, used as the value
 * returned by some ReturnStmt of `f`.
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
 * `gs` jumps to a cleanup label whose block ultimately returns `err`.
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
 * Failure check: `if (!expr)` or `if (expr == 0)` / `if (0 == expr)`.
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
 * The then-branch of a failure-check IfStmt performs a `goto cleanup`
 * without assigning anything to `err` first.
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
  // exclude trivial functions: require some other path that does assign err
  exists(Assignment a2 |
    a2.getEnclosingFunction() = f and
    a2.getLValue().(VariableAccess).getTarget() = err
  )
select is, "Failure check jumps to cleanup label without assigning error code; function returns success ($@) on this failure path.", err, err.getName()
