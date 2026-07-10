/**
 * @name  rq3-c2-lin-1-rep5
 * @id    cpp/rq3/c2/lin-1-rep5
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects missing of_node_put() on device nodes acquired via
 *              of_parse_phandle() before an exit control-flow node.
 */
import cpp

predicate isTargetApiCall(FunctionCall fc) {
  fc.getTarget().getName() = "of_parse_phandle"
}

predicate isPostOpCallOn(FunctionCall release, Expr resource) {
  release.getTarget().getName() = "of_node_put" and
  release.getArgument(0) = resource
}

predicate criticalVarAcquired(LocalVariable v, FunctionCall acquire) {
  isTargetApiCall(acquire) and
  exists(Assignment a |
    a.getRValue() = acquire and
    a.getLValue() = v.getAnAccess()
  )
}

predicate missingReleaseOnExit(FunctionCall acquire, LocalVariable v, ControlFlowNode exit) {
  criticalVarAcquired(v, acquire) and
  acquire.getASuccessor+() = exit and
  (
    exit instanceof ReturnStmt or
    exit instanceof BreakStmt or
    exit instanceof ContinueStmt or
    exit instanceof GotoStmt
  ) and
  not exists(FunctionCall release |
    isPostOpCallOn(release, v.getAnAccess()) and
    acquire.getASuccessor+() = release and
    release.getASuccessor+() = exit
  )
}

from FunctionCall acquire, LocalVariable v, ControlFlowNode exit
where missingReleaseOnExit(acquire, v, exit)
select exit, "Possible missing of_node_put() for $@ acquired by of_parse_phandle before this control-flow exit.", v, v.getName()
