/**
 * @name  rq3-c2-err-1-rep1
 * @id    cpp/rq3/c2/err-1-rep1
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects missing error return code: a function with an int err
 *              variable initialized to 0 that returns err, has a NULL-check
 *              on a call result whose then-branch jumps via goto without
 *              assigning err first.
 */
import cpp

predicate isErrorRetVar(LocalVariable v, Function f) {
  v.getFunction() = f and
  v.getName() = "err" and
  v.getType().getUnspecifiedType() instanceof IntType and
  exists(ReturnStmt r | r.getEnclosingFunction() = f and r.getExpr() = v.getAnAccess())
}

predicate initializedToZero(LocalVariable v) {
  exists(Expr init | init = v.getInitializer().getExpr() | init.getValue().toInt() = 0)
}

predicate isNullCheckOnCallResult(IfStmt ifs, FunctionCall fc) {
  exists(LocalVariable v |
    v.getAnAssignedValue() = fc and
    (
      ifs.getCondition().(NotExpr).getOperand() = v.getAnAccess()
      or
      exists(EQExpr eq |
        eq = ifs.getCondition() and
        eq.getAnOperand() = v.getAnAccess() and
        eq.getAnOperand().getValue().toInt() = 0
      )
    )
  )
}

predicate gotoInsideThen(IfStmt ifs, GotoStmt g) {
  g.getParent*() = ifs.getThen()
}

predicate noErrAssignBeforeGoto(IfStmt ifs, GotoStmt g, LocalVariable err) {
  gotoInsideThen(ifs, g) and
  not exists(Assignment a |
    a.getLValue() = err.getAnAccess() and
    a.getParent*() = ifs.getThen() and
    a.getLocation().getStartLine() <= g.getLocation().getStartLine()
  )
}

predicate missingErrorReturnCode(Function f, IfStmt ifs, LocalVariable err) {
  isErrorRetVar(err, f) and
  initializedToZero(err) and
  ifs.getEnclosingFunction() = f and
  exists(FunctionCall fc | isNullCheckOnCallResult(ifs, fc)) and
  exists(GotoStmt g | noErrAssignBeforeGoto(ifs, g, err))
}

from Function f, IfStmt ifs, LocalVariable err
where missingErrorReturnCode(f, ifs, err)
select ifs, "Possible missing error return code: '" + err.getName() + "' is not assigned a negative errno before goto on error path in " + f.getName() + "."
