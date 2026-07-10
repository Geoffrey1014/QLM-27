/**
 * @name  rq3-c2-lin-3-rep1
 * @id    cpp/rq3/c2/lin-3-rep1
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects refcount leaks: of_parse_phandle() returns a node with
 *              incremented refcount that must be released via of_node_put()
 *              on every path, including error returns.
 */

import cpp

predicate acquires_node(FunctionCall acq, Variable v) {
  acq.getTarget().getName() = "of_parse_phandle" and
  (
    exists(AssignExpr a |
      a.getRValue() = acq and
      a.getLValue() = v.getAnAccess()
    )
    or
    exists(Initializer init |
      init.getExpr() = acq and
      init.getDeclaration() = v
    )
  )
}

predicate releases_node(FunctionCall rel, Variable v) {
  rel.getTarget().getName() = "of_node_put" and
  rel.getArgument(0) = v.getAnAccess()
}

predicate early_exit_without_release(Variable v, FunctionCall acq, ReturnStmt r) {
  acquires_node(acq, v) and
  r.getEnclosingFunction() = acq.getEnclosingFunction() and
  acq.(ControlFlowNode).getASuccessor+() = r and
  not exists(FunctionCall rel |
    releases_node(rel, v) and
    acq.(ControlFlowNode).getASuccessor+() = rel and
    rel.(ControlFlowNode).getASuccessor+() = r
  )
}

predicate leaky_function(Function f, Variable v, FunctionCall acq) {
  acquires_node(acq, v) and
  acq.getEnclosingFunction() = f and
  exists(ReturnStmt r | early_exit_without_release(v, acq, r))
}

from Function f, Variable v, FunctionCall acq
where leaky_function(f, v, acq)
select acq,
  "Possible refcount leak: '" + v.getName() +
  "' acquired via of_parse_phandle here may not be released via of_node_put on all paths in '" +
  f.getName() + "'."
