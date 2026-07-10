/**
 * @name  rq3-c2-lu-5-rep3
 * @id    cpp/rq3/c2/lu-5-rep3
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects memory leaks where kstrdup() result is not freed
 *              on all return paths (pattern from affs_remount bug
 *              fixed in commit 450c3d416683).
 */

import cpp

predicate isResourceAcquire(FunctionCall fc, Variable v) {
  fc.getTarget().hasName("kstrdup") and
  exists(AssignExpr ae |
    ae.getRValue() = fc and
    ae.getLValue() = v.getAnAccess())
}

predicate isCleanupCall(FunctionCall fc, Variable v) {
  fc.getTarget().hasName("kfree") and
  fc.getArgument(0) = v.getAnAccess()
}

predicate returnReachableFromAcquire(FunctionCall acquire, ReturnStmt ret, Variable v) {
  isResourceAcquire(acquire, v) and
  acquire.getEnclosingFunction() = ret.getEnclosingFunction() and
  acquire.getASuccessor+() = ret
}

predicate leakOnPath(FunctionCall acquire, ReturnStmt ret, Variable v) {
  returnReachableFromAcquire(acquire, ret, v) and
  not exists(FunctionCall cleanup |
    isCleanupCall(cleanup, v) and
    cleanup.getEnclosingFunction() = acquire.getEnclosingFunction() and
    acquire.getASuccessor+() = cleanup and
    cleanup.getASuccessor+() = ret)
}

from FunctionCall acquire, ReturnStmt ret, Variable v
where leakOnPath(acquire, ret, v)
select ret,
  "Potential memory leak: variable '" + v.getName() +
  "' from kstrdup() at $@ is not freed on this return path.",
  acquire, acquire.toString()
