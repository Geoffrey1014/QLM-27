/**
 * @name  rq3-c2-err-1-rep5
 * @id    cpp/rq3/c2/err-1-rep5
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects functions returning an error variable initialized to 0,
 *              where a failure check branches to a cleanup label without first
 *              assigning a negative error code to the return variable.
 */

import cpp

predicate isErrorReturnVar(LocalVariable v) {
  v.getType().getUnderlyingType() instanceof IntegralType and
  exists(Expr init | init = v.getInitializer().getExpr() and init.getValue() = "0") and
  v.getName().regexpMatch("(?i)err|ret|rc|error|status|result") and
  exists(ReturnStmt rs |
    rs.getExpr().(VariableAccess).getTarget() = v and
    rs.getEnclosingFunction() = v.getFunction()
  )
}

predicate isCleanupGoto(GotoStmt gs) {
  gs.getName().regexpMatch("(?i)(out|err|fail|cleanup|done|exit|free|unlock).*")
}

predicate isFailureCheckIf(IfStmt ifs) {
  ifs.getCondition() instanceof NotExpr
  or
  ifs.getCondition() instanceof EqualityOperation
  or
  ifs.getCondition() instanceof RelationalOperation
  or
  exists(FunctionCall fc |
    fc = ifs.getCondition() and
    fc.getTarget().getName().regexpMatch("IS_ERR.*|.*_failed|.*_error")
  )
}

predicate gotoOnFailurePath(IfStmt ifs, GotoStmt gs) {
  isCleanupGoto(gs) and
  isFailureCheckIf(ifs) and
  gs.getParentStmt*() = ifs.getThen()
}

predicate assignsErrorBeforeGoto(IfStmt ifs, GotoStmt gs, LocalVariable v) {
  isErrorReturnVar(v) and
  exists(AssignExpr ae |
    ae.getLValue().(VariableAccess).getTarget() = v and
    ae.getEnclosingStmt().getParentStmt*() = ifs.getThen() and
    ae.getLocation().getStartLine() < gs.getLocation().getStartLine()
  )
}

predicate missingErrorAssignment(Function f, LocalVariable v, IfStmt ifs, GotoStmt gs) {
  isErrorReturnVar(v) and
  v.getFunction() = f and
  ifs.getEnclosingFunction() = f and
  gs.getEnclosingFunction() = f and
  gotoOnFailurePath(ifs, gs) and
  not assignsErrorBeforeGoto(ifs, gs, v) and
  exists(ReturnStmt rs |
    rs.getEnclosingFunction() = f and
    rs.getExpr().(VariableAccess).getTarget() = v and
    rs.getLocation().getStartLine() > gs.getLocation().getStartLine()
  ) and
  not exists(ReturnStmt rs2 |
    rs2.getParentStmt*() = ifs.getThen() and
    exists(rs2.getExpr().getValue()) and
    rs2.getExpr().getValue() != "0"
  )
}

from Function f, LocalVariable v, IfStmt ifs, GotoStmt gs
where missingErrorAssignment(f, v, ifs, gs)
select gs,
  "Goto to cleanup label on a failure path without assigning an error code to '" +
    v.getName() + "', which will cause the function to return success."
