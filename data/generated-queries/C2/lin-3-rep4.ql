/**
 * @name  rq3-c2-lin-3-rep4
 * @id    cpp/rq3/c2/lin-3-rep4
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects of_parse_phandle refcount leaks on return paths
 *              where of_node_put was not invoked.
 */
import cpp

predicate isAcquireCall(FunctionCall acq) {
  acq.getTarget().getName() = "of_parse_phandle"
}

predicate acquiredVariable(FunctionCall acq, Variable v) {
  isAcquireCall(acq) and
  exists(AssignExpr a |
    a.getRValue() = acq and
    a.getLValue() = v.getAnAccess())
}

predicate isReleaseCallOn(FunctionCall rel, Variable v) {
  rel.getTarget().getName() = "of_node_put" and
  rel.getArgument(0) = v.getAnAccess()
}

predicate returnsWithoutRelease(FunctionCall acq, Variable v, ReturnStmt ret) {
  acquiredVariable(acq, v) and
  ret.getEnclosingFunction() = acq.getEnclosingFunction() and
  acq.getASuccessor*() = ret and
  not exists(FunctionCall rel |
    isReleaseCallOn(rel, v) and
    acq.getASuccessor*() = rel and
    rel.getASuccessor*() = ret)
}

predicate leakingAcquire(FunctionCall acq, Variable v, ReturnStmt ret) {
  returnsWithoutRelease(acq, v, ret) and
  v.getType().getUnspecifiedType().(PointerType).getBaseType().getName() = "device_node"
}

from FunctionCall acq, Variable v, ReturnStmt ret
where leakingAcquire(acq, v, ret)
select ret, "Possible refcount leak: '" + v.getName() + "' acquired by '" + acq.getTarget().getName() + "' may not be released before this return."
