/**
 * @name  rq3-c2-lin-3-rep3
 * @id    cpp/rq3/c2/lin-3-rep3
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects missing of_node_put after of_parse_phandle on some return path.
 */
import cpp

predicate acquiresNode(FunctionCall c, Variable v) {
  c.getTarget().getName() = "of_parse_phandle" and
  exists(AssignExpr a |
    a.getRValue() = c and
    a.getLValue() = v.getAnAccess())
}

predicate releasesNode(FunctionCall c, Variable v) {
  c.getTarget().getName() = "of_node_put" and
  c.getArgument(0) = v.getAnAccess()
}

predicate returnReachableFrom(FunctionCall acq, ReturnStmt ret) {
  acq.getEnclosingFunction() = ret.getEnclosingFunction() and
  acq.(ControlFlowNode).getASuccessor+() = ret
}

predicate noReleaseOnPath(FunctionCall acq, Variable v, ReturnStmt ret) {
  returnReachableFrom(acq, ret) and
  not exists(FunctionCall rel |
    releasesNode(rel, v) and
    acq.(ControlFlowNode).getASuccessor+() = rel and
    rel.(ControlFlowNode).getASuccessor+() = ret)
}

from FunctionCall acq, Variable v, ReturnStmt ret
where
  acquiresNode(acq, v) and
  noReleaseOnPath(acq, v, ret)
select acq, "Missing of_node_put on variable '" + v.getName() + "' before return at $@.", ret, ret.toString()
