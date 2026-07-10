/**
 * @name  rq3-c2-err-2-rep3
 * @id    cpp/rq3/c2/err-2-rep3
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects missing error return code on goto in error-handling branches
 *              (pattern of commit 45c7eaeb29d6: thermal_of_populate_bind_params).
 */

import cpp

predicate isErrnoReturningFunction(Function f) {
  f.getType().getUnspecifiedType() instanceof IntType and
  exists(ReturnStmt rs |
    rs.getEnclosingFunction() = f and
    rs.getExpr().getValue().toInt() < 0
  )
}

predicate isFailureCheck(IfStmt ifs, Variable retVar) {
  retVar.getType().getUnspecifiedType() instanceof IntType and
  exists(Function f |
    ifs.getEnclosingFunction() = f and
    isErrnoReturningFunction(f) and
    exists(ReturnStmt rs |
      rs.getEnclosingFunction() = f and
      rs.getExpr() = retVar.getAnAccess()
    )
  ) and
  (
    ifs.getCondition() instanceof NotExpr
    or
    exists(RelationalOperation ro | ro = ifs.getCondition())
    or
    exists(EQExpr eq | eq = ifs.getCondition())
    or
    exists(FunctionCall fc |
      fc = ifs.getCondition() and
      fc.getTarget().getName().matches("IS\\_ERR%")
    )
  )
}

predicate gotoSkipsRetAssignment(GotoStmt g, Variable retVar) {
  retVar.getType().getUnspecifiedType() instanceof IntType and
  g.getEnclosingFunction() = retVar.getAnAccess().getEnclosingFunction() and
  exists(ReturnStmt rs |
    rs.getEnclosingFunction() = g.getEnclosingFunction() and
    rs.getExpr() = retVar.getAnAccess()
  ) and
  not exists(AssignExpr ae, ExprStmt es, BlockStmt parentBlock |
    ae.getLValue() = retVar.getAnAccess() and
    ae.getEnclosingStmt() = es and
    es.getParentStmt() = parentBlock and
    g.getParentStmt() = parentBlock and
    es.getLocation().getStartLine() < g.getLocation().getStartLine()
  )
}

predicate missingErrorCodeOnGoto(IfStmt ifs, GotoStmt g, Variable retVar, Function f) {
  f = ifs.getEnclosingFunction() and
  isErrnoReturningFunction(f) and
  isFailureCheck(ifs, retVar) and
  gotoSkipsRetAssignment(g, retVar) and
  g.getEnclosingFunction() = f and
  g.getParent*() = ifs.getThen() and
  retVar instanceof LocalVariable and
  exists(retVar.getAnAccess())
}

from IfStmt ifs, GotoStmt g, Variable retVar, Function f
where missingErrorCodeOnGoto(ifs, g, retVar, f)
select g,
  "Goto in error branch of " + f.getName() +
  " does not assign negative errno to ret variable '" + retVar.getName() +
  "' before jumping."
