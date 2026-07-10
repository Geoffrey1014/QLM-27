/**
 * @name Error path jumps to cleanup without setting error return code
 * @description A function returning int contains an error-handling branch
 *              (the body of an `if (!x)` / `if (x == 0)` check after an
 *              allocation- or count-style call) that performs `goto
 *              <cleanup>` without assigning a non-zero (error) value to
 *              the variable that is subsequently returned at the cleanup
 *              label. The cleanup label flows to `return ret;`, so the
 *              caller silently observes success (ret == 0) for the
 *              failure case.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-err-2
 */

import cpp

/** A call whose result typically indicates allocation success / element count. */
predicate isResourceOrCountCall(FunctionCall fc) {
  exists(string n | n = fc.getTarget().getName() |
    n.matches("k%alloc%") or
    n.matches("%alloc%") or
    n.matches("of_count_%") or
    n.matches("of_get_%") or
    n.matches("of_parse_phandle%") or
    n.matches("%_count_%")
  )
}

/** `e` is a null-or-zero check on `v`: `!v`, `v == 0`, `v == NULL`, `v <= 0`. */
predicate isNullOrZeroCheck(Expr e, Variable v) {
  e.(NotExpr).getOperand() = v.getAnAccess()
  or
  exists(EQExpr eq | eq = e |
    eq.getAnOperand() = v.getAnAccess() and
    eq.getAnOperand().getValue() = "0"
  )
  or
  exists(LEExpr le | le = e |
    le.getLeftOperand() = v.getAnAccess() and
    le.getRightOperand().getValue() = "0"
  )
}

/** `g` jumps to a label whose statements reach `return retVar;`. */
predicate gotoReachesReturnOfVar(GotoStmt g, Variable retVar) {
  exists(ReturnStmt r |
    r.getEnclosingFunction() = g.getEnclosingFunction() and
    r.getExpr() = retVar.getAnAccess() and
    g.getASuccessor+() = r
  )
}

/** Between the if-branch entry `b` and the goto `g`, there is no assignment
 *  of a non-zero RHS to `retVar`. */
predicate noErrorAssignBetween(Stmt b, GotoStmt g, Variable retVar) {
  not exists(AssignExpr a |
    a.getLValue() = retVar.getAnAccess() and
    not a.getRValue().getValue() = "0" and
    b.getASuccessor*() = a and
    a.getASuccessor*() = g
  )
}

from
  Function f, FunctionCall acq, Variable resVar, IfStmt ifs, GotoStmt g,
  ReturnStmt finalRet, Variable retVar
where
  // Function returns int (an error code by convention).
  f = g.getEnclosingFunction() and
  f.getType().getUnspecifiedType().getName() = "int" and
  // Some acquire / count-style call assigns / initializes resVar.
  isResourceOrCountCall(acq) and
  acq.getEnclosingFunction() = f and
  (
    exists(AssignExpr ae |
      ae.getEnclosingFunction() = f and
      ae.getLValue() = resVar.getAnAccess() and
      ae.getRValue() = acq
    )
    or
    exists(Initializer init |
      init.getDeclaration() = resVar and init.getExpr() = acq
    )
  ) and
  // An if-statement immediately checks resVar for null/zero.
  ifs.getEnclosingFunction() = f and
  isNullOrZeroCheck(ifs.getControllingExpr(), resVar) and
  // The goto sits inside the then-branch of that if.
  g.getParent*() = ifs.getThen() and
  // The function returns some local variable retVar at the end (via cleanup label).
  finalRet.getEnclosingFunction() = f and
  finalRet.getExpr() = retVar.getAnAccess() and
  retVar instanceof LocalVariable and
  // Cleanup label reached by the goto eventually returns retVar.
  gotoReachesReturnOfVar(g, retVar) and
  // retVar is the function's int return variable (matches return type).
  retVar.getType().getUnspecifiedType().getName() = "int" and
  // No error assignment to retVar between if-branch and the goto.
  noErrorAssignBetween(ifs.getThen(), g, retVar) and
  // Exclude the resource variable itself being the returned one.
  retVar != resVar
select g,
  "Error path goto in `" + f.getName() + "` jumps to cleanup without setting `" +
    retVar.getName() + "`; failed `" + acq.getTarget().getName() +
    "()` will be reported as success (returned 0)."
