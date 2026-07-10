/**
 * @name Missing error code on goto-to-cleanup path
 * @description An if-block detects an error condition (failed allocation,
 *              missing/zero return from a query) and jumps via `goto` to a
 *              cleanup label that returns a status variable. If the status
 *              variable is not assigned an error code before the goto, the
 *              function silently returns success (the previously-held value
 *              of the status variable, usually 0) despite the error path.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-err-2
 * @tags correctness
 *       error-handling
 */

import cpp

/** A local variable used as the function's error-status return value. */
predicate isStatusVar(LocalVariable ret, Function f) {
  ret.getFunction() = f and
  ret.getType().getUnspecifiedType() instanceof IntegralType and
  // Function returns the variable (somewhere in its body)
  exists(ReturnStmt rs |
    rs.getEnclosingFunction() = f and
    rs.getExpr().(VariableAccess).getTarget() = ret
  )
}

/** An expression that looks like an error condition for `e` (the value being checked). */
predicate isErrorCheckExpr(Expr cond, Expr checked) {
  // `!x`  — x is null / zero / falsy
  exists(NotExpr ne | ne = cond and ne.getOperand() = checked)
  or
  // `x == 0` or `0 == x`
  exists(EQExpr eq | eq = cond and
    (eq.getLeftOperand() = checked and eq.getRightOperand().getValue() = "0" or
     eq.getRightOperand() = checked and eq.getLeftOperand().getValue() = "0"))
  or
  // `x < 0`
  exists(LTExpr lt | lt = cond and
    lt.getLeftOperand() = checked and lt.getRightOperand().getValue() = "0")
  or
  // `x <= 0`
  exists(LEExpr le | le = cond and
    le.getLeftOperand() = checked and le.getRightOperand().getValue() = "0")
}

/** `checked` originates from a call to a function that returns a resource / status. */
predicate looksLikeAcquisitionResult(Expr checked) {
  // direct: `x = call(); if (!x)` — the checked variable was last assigned a call result
  exists(LocalVariable v, FunctionCall fc |
    checked.(VariableAccess).getTarget() = v and
    fc.getEnclosingFunction() = checked.getEnclosingFunction() and
    exists(AssignExpr ae |
      ae.getLValue().(VariableAccess).getTarget() = v and
      ae.getRValue() = fc and
      ae.getLocation().getStartLine() < checked.getLocation().getStartLine()
    )
  )
  or
  // direct: the checked expression itself is a call
  checked instanceof FunctionCall
}

/** `s` is a goto that targets `lbl`. */
predicate gotoTo(GotoStmt s, LabelStmt lbl) {
  s.getTarget() = lbl
}

/** Statement `s` directly assigns to `ret` (status variable). */
predicate assignsRet(Stmt s, LocalVariable ret) {
  exists(AssignExpr ae |
    ae.getEnclosingStmt() = s and
    ae.getLValue().(VariableAccess).getTarget() = ret
  )
  or
  exists(DeclStmt ds, Variable v |
    ds = s and v = ret and
    v.getInitializer().getExpr() instanceof Expr
  )
}

/** The IfStmt's then-branch (a block) reaches a goto-cleanup with NO assignment to ret in between. */
predicate badIfBranch(IfStmt ifs, GotoStmt g, LocalVariable ret) {
  g.getParentStmt*() = ifs.getThen() and
  not exists(AssignExpr ae |
    ae.getEnclosingFunction() = ifs.getEnclosingFunction() and
    ae.getLValue().(VariableAccess).getTarget() = ret and
    // assignment appears textually inside the then-branch and before the goto
    ae.getLocation().getStartLine() >= ifs.getThen().getLocation().getStartLine() and
    ae.getLocation().getStartLine() <= g.getLocation().getStartLine()
  )
}

from Function f, LocalVariable ret, IfStmt ifs, GotoStmt g, LabelStmt lbl,
     Expr cond, Expr checked
where
  isStatusVar(ret, f) and
  ifs.getEnclosingFunction() = f and
  ifs.getCondition() = cond and
  isErrorCheckExpr(cond, checked) and
  looksLikeAcquisitionResult(checked) and
  g.getEnclosingFunction() = f and
  gotoTo(g, lbl) and
  badIfBranch(ifs, g, ret) and
  // Exclude cases where the checked expression IS the status variable itself
  // (e.g. `if (ret < 0) goto cleanup;` — ret already holds an error value).
  not checked.(VariableAccess).getTarget() = ret and
  // The label that g targets eventually returns `ret` (cleanup-and-return label).
  exists(ReturnStmt rs |
    rs.getEnclosingFunction() = f and
    rs.getExpr().(VariableAccess).getTarget() = ret and
    rs.getLocation().getStartLine() > lbl.getLocation().getStartLine()
  ) and
  // `ret` was last assigned a non-error (success-ish) value before this if:
  // i.e. somewhere earlier in the function, `ret` was assigned a value that is
  // NOT an error constant. We approximate by requiring at least one earlier
  // assignment to `ret` (so the function is not freshly initialised to an
  // error code right before this branch).
  exists(AssignExpr prior |
    prior.getEnclosingFunction() = f and
    prior.getLValue().(VariableAccess).getTarget() = ret and
    prior.getLocation().getStartLine() < ifs.getLocation().getStartLine()
  )
select ifs, "Error path goto '" + lbl.getName() +
  "' without assigning error code to status variable '" + ret.getName() +
  "'; function will silently return success."
