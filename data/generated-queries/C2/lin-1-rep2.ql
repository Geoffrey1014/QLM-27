/**
 * @name  rq3-c2-lin-1-rep2
 * @id    cpp/rq3/c2/lin-1-rep2
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2 — device_node refcount leak from of_parse_phandle without of_node_put on early-exit paths.
 */
import cpp

predicate is_target_acquire(FunctionCall c) {
  c.getTarget().getName() = "of_parse_phandle"
}

predicate is_release_of(FunctionCall c, Variable v) {
  c.getTarget().getName() = "of_node_put" and
  c.getArgument(0).(VariableAccess).getTarget() = v
}

predicate acquired_into(FunctionCall acq, Variable v) {
  is_target_acquire(acq) and
  (
    exists(AssignExpr a |
      a.getRValue() = acq and
      a.getLValue().(VariableAccess).getTarget() = v
    )
    or
    exists(Initializer init |
      init.getExpr() = acq and init.getDeclaration() = v
    )
  )
}

predicate early_exit_after(FunctionCall acq, Variable v, Stmt exitStmt) {
  acquired_into(acq, v) and
  (
    exitStmt instanceof ContinueStmt or
    exitStmt instanceof BreakStmt or
    exitStmt instanceof ReturnStmt
  ) and
  exitStmt.getEnclosingFunction() = acq.getEnclosingFunction() and
  acq.getLocation().getStartLine() < exitStmt.getLocation().getStartLine() and
  not exists(FunctionCall rel |
    is_release_of(rel, v) and
    rel.getEnclosingFunction() = acq.getEnclosingFunction() and
    rel.getLocation().getStartLine() > acq.getLocation().getStartLine() and
    rel.getLocation().getStartLine() <= exitStmt.getLocation().getStartLine()
  )
}

from FunctionCall acq, Variable v, Stmt exitStmt
where early_exit_after(acq, v, exitStmt)
select acq, "device_node from of_parse_phandle stored in '" + v.getName() + "' may leak on exit via $@ (no of_node_put on this path)", exitStmt, exitStmt.toString()
