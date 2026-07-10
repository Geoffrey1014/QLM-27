/**
 * @name Missing error-return-code on early NULL-check goto (L0 err-1-rep4)
 * @description A function initialises an integer error variable to 0, calls
 *              a getter API, checks the result, and jumps via `goto <label>`
 *              to a cleanup block that returns the error variable — but the
 *              conditional branch never assigns a non-zero errno to that
 *              variable, so the caller sees success on a real failure path.
 * @kind problem
 * @problem.severity warning
 * @id qlm/l0/err-1-rep4-missing-err-return-code
 */

import cpp

predicate errRetZeroInitAndReturned(Function f, LocalVariable errVar) {
  f.fromSource() and
  errVar.getFunction() = f and
  errVar.getType().getUnspecifiedType() instanceof IntegralType and
  exists(Expr initExpr |
    initExpr = errVar.getInitializer().getExpr() and
    initExpr.getValue() = "0"
  ) and
  exists(ReturnStmt rs |
    rs.getEnclosingFunction() = f and
    rs.getExpr().(VariableAccess).getTarget() = errVar
  )
}

from Function f, LocalVariable errVar, GotoStmt g, IfStmt ifs, BlockStmt thenBlk
where
  errRetZeroInitAndReturned(f, errVar) and
  g.getEnclosingFunction() = f and
  (
    ifs.getThen() = g
    or
    (ifs.getThen() = thenBlk and thenBlk.getStmt(0) = g)
  ) and
  not exists(VariableAccess va |
    va = ifs.getCondition().getAChild*() and
    va.getTarget() = errVar
  ) and
  not exists(ExprStmt es, Assignment a |
    ifs.getThen() = thenBlk and
    thenBlk.getAStmt() = es and
    es.getExpr() = a and
    a.getLValue().(VariableAccess).getTarget() = errVar
  )
select g,
  "Function '" + f.getName() + "' may reach cleanup label with `" + errVar.getName() +
    "` still 0 on a failure branch — caller sees success on failure."
