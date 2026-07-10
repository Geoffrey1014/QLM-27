/**
 * @name  rq3-c2-err-1-rep3
 * @id    cpp/rq3/c2/err-1-rep3
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 */
import cpp

predicate isErrVariable(LocalVariable err) {
  err.getType().getUnspecifiedType() instanceof IntType and
  err.getName().regexpMatch("err|ret|rc|error|status")
}

predicate hasZeroInitializer(LocalVariable err) {
  exists(Expr init | init = err.getInitializer().getExpr() |
    init.getValue() = "0"
  )
}

predicate returnsErrAtEnd(Function f, LocalVariable err) {
  err.getFunction() = f and
  exists(ReturnStmt ret | ret.getEnclosingFunction() = f |
    ret.getExpr() = err.getAnAccess()
  )
}

predicate gotoTargetReturnsErr(GotoStmt g, LocalVariable err) {
  exists(LabelStmt lbl, ReturnStmt ret |
    lbl = g.getTarget() and
    ret.getEnclosingFunction() = g.getEnclosingFunction() and
    ret.getExpr() = err.getAnAccess() and
    // label appears before return in same function
    lbl.getLocation().getStartLine() <= ret.getLocation().getStartLine()
  )
}

predicate gotoInsideIfCheck(GotoStmt g) {
  exists(IfStmt ifs |
    g.getParent*() = ifs.getThen() and
    not exists(IfStmt inner | inner != ifs and g.getParent*() = inner.getThen() and inner.getParent*() = ifs.getThen())
  )
}

predicate errNotAssignedBeforeGoto(GotoStmt g, LocalVariable err) {
  err.getFunction() = g.getEnclosingFunction() and
  not exists(Assignment a |
    a.getLValue() = err.getAnAccess() and
    a.getLocation().getStartLine() < g.getLocation().getStartLine() and
    a.getEnclosingFunction() = g.getEnclosingFunction() and
    not a.getRValue().getValue() = "0"
  ) and
  // require the goto comes after the zero init
  exists(Expr init | init = err.getInitializer().getExpr() |
    init.getLocation().getStartLine() < g.getLocation().getStartLine()
  )
}

from Function f, LocalVariable err, GotoStmt g
where
  isErrVariable(err) and
  hasZeroInitializer(err) and
  returnsErrAtEnd(f, err) and
  err.getFunction() = f and
  g.getEnclosingFunction() = f and
  gotoTargetReturnsErr(g, err) and
  gotoInsideIfCheck(g) and
  errNotAssignedBeforeGoto(g, err)
select g, "Goto to error-return label without assigning nonzero error code to " + err.getName()
