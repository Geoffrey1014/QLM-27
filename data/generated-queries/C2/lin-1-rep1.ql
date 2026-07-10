/**
 * @name  rq3-c2-lin-1-rep1
 * @id    cpp/rq3/c2/lin-1-rep1
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2 — device_node refcount leak from of_parse_phandle without of_node_put on all paths.
 */
import cpp

predicate acquires_node(FunctionCall acq, Expr nodeExpr) {
  acq.getTarget().getName() = "of_parse_phandle" and
  (
    exists(AssignExpr a | a.getRValue() = acq and nodeExpr = a.getLValue())
    or
    exists(Variable v | v.getInitializer().getExpr() = acq and nodeExpr = v.getAnAccess())
  )
}

predicate releases_node(FunctionCall rel, Expr nodeExpr) {
  rel.getTarget().getName() = "of_node_put" and
  nodeExpr = rel.getArgument(0)
}

predicate same_node(Expr a, Expr b) {
  exists(Variable v |
    a = v.getAnAccess() and b = v.getAnAccess()
  )
}

predicate reaches_without_release(FunctionCall acq, Expr acqNode, Stmt exitStmt) {
  acquires_node(acq, acqNode) and
  (exitStmt instanceof ContinueStmt or exitStmt instanceof BreakStmt or exitStmt instanceof ReturnStmt) and
  acq.getEnclosingFunction() = exitStmt.getEnclosingFunction() and
  acq.getLocation().getStartLine() < exitStmt.getLocation().getStartLine() and
  not exists(FunctionCall rel, Expr relNode |
    releases_node(rel, relNode) and
    same_node(acqNode, relNode) and
    rel.getEnclosingFunction() = acq.getEnclosingFunction() and
    rel.getLocation().getStartLine() > acq.getLocation().getStartLine() and
    rel.getLocation().getStartLine() <= exitStmt.getLocation().getStartLine()
  )
}

predicate leak_at(FunctionCall acq, Stmt exitStmt) {
  exists(Expr acqNode | reaches_without_release(acq, acqNode, exitStmt))
}

from FunctionCall acq, Stmt exitStmt
where leak_at(acq, exitStmt)
select acq, "device_node from of_parse_phandle may leak: exit via $@ without of_node_put", exitStmt, exitStmt.toString()
