/**
 * @name  rq3-c2-lin-4-rep3
 * @id    cpp/rq3/c2/lin-4-rep3
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 */
import cpp

predicate acquiresNode(FunctionCall acq, Variable v) {
  acq.getTarget().getName() = "of_parse_phandle" and
  exists(Assignment a |
    a.getRValue() = acq and
    a.getLValue() = v.getAnAccess()
  )
}

predicate releasesNode(FunctionCall rel, Variable v) {
  rel.getTarget().getName() = "of_node_put" and
  rel.getArgument(0) = v.getAnAccess()
}

predicate returnAfterAcquire(FunctionCall acq, Variable v, ReturnStmt ret) {
  acquiresNode(acq, v) and
  acq.getEnclosingFunction() = ret.getEnclosingFunction() and
  exists(ControlFlowNode cfn |
    cfn = acq and
    cfn.getASuccessor+() = ret
  )
}

predicate missingReleaseOnReturn(FunctionCall acq, Variable v, ReturnStmt ret) {
  returnAfterAcquire(acq, v, ret) and
  not exists(FunctionCall rel |
    releasesNode(rel, v) and
    rel.getEnclosingFunction() = ret.getEnclosingFunction() and
    acq.(ControlFlowNode).getASuccessor+() = rel and
    rel.(ControlFlowNode).getASuccessor*() = ret
  )
}

from FunctionCall acq, Variable v, ReturnStmt ret
where missingReleaseOnReturn(acq, v, ret)
select ret, "Possible refcount leak: '" + v.getName() + "' acquired by " + acq.getTarget().getName() + " not released before return."
