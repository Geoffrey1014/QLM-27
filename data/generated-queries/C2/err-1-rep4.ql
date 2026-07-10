/**
 * @name  rq3-c2-err-1-rep4
 * @id    cpp/rq3/c2/err-1-rep4
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects error-return-code bugs where a goto in a null/error
 *              check branch fails to set the err variable before jumping to
 *              a cleanup label that returns the (still-zero) err.
 */
import cpp

predicate errReturningFunction(Function f) {
  f.getType().getUnderlyingType() instanceof IntType and
  exists(ReturnStmt r | r.getEnclosingFunction() = f)
}

predicate zeroInitErrVariable(Function f, LocalVariable v) {
  errReturningFunction(f) and
  v.getFunction() = f and
  v.getType().getUnderlyingType() instanceof IntType and
  exists(Expr init | init = v.getInitializer().getExpr() and init.getValue() = "0") and
  exists(ReturnStmt r | r.getEnclosingFunction() = f and r.getExpr() = v.getAnAccess())
}

predicate gotoInNullCheckWithoutErrAssign(Function f, LocalVariable err, GotoStmt g) {
  zeroInitErrVariable(f, err) and
  g.getEnclosingFunction() = f and
  exists(IfStmt ifs |
    ifs.getThen() = g.getParent*() and
    ifs.getCondition() instanceof NotExpr
  ) and
  not exists(Assignment a |
    a.getEnclosingFunction() = f and
    a.getLValue() = err.getAnAccess() and
    a = g.getParent*()
  )
}

predicate gotoTargetReturnsErr(GotoStmt g, LocalVariable err) {
  exists(Function f |
    gotoInNullCheckWithoutErrAssign(f, err, g) and
    exists(ReturnStmt r |
      r.getEnclosingFunction() = f and
      r.getExpr() = err.getAnAccess()
    )
  )
}

from Function f, LocalVariable err, GotoStmt g
where
  gotoInNullCheckWithoutErrAssign(f, err, g) and
  gotoTargetReturnsErr(g, err)
select g, "Goto in null/error check branch does not assign error code to '" + err.getName() + "', which is returned as 0 (success)."
