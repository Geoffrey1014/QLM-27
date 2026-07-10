/**
 * @name  rq3-c2-lin-3-rep2
 * @id    cpp/rq3/c2/lin-3-rep2
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects missing of_node_put on of_parse_phandle return value
 *              on early-return paths (refcount leak).
 */

import cpp

predicate is_target_acquire(FunctionCall acq, Variable v) {
  acq.getTarget().getName() = "of_parse_phandle" and
  exists(VariableAccess va |
    va = acq.getParent().(AssignExpr).getLValue() and
    va.getTarget() = v
  )
  or
  acq.getTarget().getName() = "of_parse_phandle" and
  exists(Initializer init |
    init.getExpr() = acq and
    init.getDeclaration() = v
  )
}

predicate is_release_call(FunctionCall rel, Variable v) {
  rel.getTarget().getName() = "of_node_put" and
  exists(VariableAccess va |
    va = rel.getArgument(0) and
    va.getTarget() = v
  )
}

predicate early_return_between(FunctionCall acq, ReturnStmt ret) {
  acq.getEnclosingFunction() = ret.getEnclosingFunction() and
  acq.getLocation().getStartLine() < ret.getLocation().getStartLine() and
  // there exists at least one statement after acq before ret (an early exit, not final return)
  exists(Stmt s |
    s.getEnclosingFunction() = acq.getEnclosingFunction() and
    s.getLocation().getStartLine() > acq.getLocation().getStartLine() and
    s.getLocation().getStartLine() < ret.getLocation().getStartLine()
  )
}

predicate release_dominates_return(FunctionCall acq, Variable v, ReturnStmt ret) {
  exists(FunctionCall rel |
    is_release_call(rel, v) and
    rel.getEnclosingFunction() = acq.getEnclosingFunction() and
    rel.getLocation().getStartLine() > acq.getLocation().getStartLine() and
    rel.getLocation().getStartLine() < ret.getLocation().getStartLine()
  )
}

predicate leaks_on_return(FunctionCall acq, Variable v, ReturnStmt ret) {
  is_target_acquire(acq, v) and
  early_return_between(acq, ret) and
  acq.getEnclosingFunction() = ret.getEnclosingFunction() and
  not release_dominates_return(acq, v, ret)
}

from FunctionCall acq, Variable v, ReturnStmt ret
where leaks_on_return(acq, v, ret)
select acq,
  "of_parse_phandle return stored in $@ may leak on early return at $@ (missing of_node_put).",
  v, v.getName(), ret, "return"
