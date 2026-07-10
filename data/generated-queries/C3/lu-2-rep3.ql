/**
 * @name C3 generated query for lu-2 / fix 2289adbfa559
 * @description Missing kfree on early-return path after kmalloc — memory leak (CWE-401)
 * @kind problem
 * @problem.severity warning
 * @id cpp/rq3/c3/lu-2-rep3
 */

import cpp

predicate isAcquisition(FunctionCall fc) {
  fc.getTarget().getName() in ["kmalloc", "kzalloc", "kcalloc", "kmalloc_array"]
}

predicate isReleaseCall(FunctionCall fc) {
  fc.getTarget().getName() in ["kfree", "kvfree", "kfree_sensitive"]
}

Variable getAcquiredVariable(FunctionCall acquire) {
  exists(AssignExpr assign |
    assign.getRValue() = acquire and
    result = assign.getLValue().(VariableAccess).getTarget()
  )
}

predicate releasesVar(FunctionCall fc, Variable v) {
  isReleaseCall(fc) and
  exists(VariableAccess va |
    va = fc.getArgument(0) and
    va.getTarget() = v
  )
}

/**
 * Holds if a ReturnStmt in the same function as `acquire` is
 * control-flow reachable from `acquire` without passing through any
 * release of `v`. This captures the leaking early-return pattern.
 */
predicate hasLeakingReturn(FunctionCall acquire, Variable v) {
  exists(ReturnStmt ret |
    ret.getEnclosingFunction() = acquire.getEnclosingFunction() and
    acquire.getASuccessor+() = ret and
    not exists(FunctionCall rel |
      releasesVar(rel, v) and
      acquire.getASuccessor+() = rel and
      rel.getASuccessor+() = ret
    )
  )
}

predicate isInFixedFunction(FunctionCall fc) {
  fc.getEnclosingFunction().getName().toLowerCase().matches("%fixed%")
}

from FunctionCall acquire, Variable acquiredVar
where
  isAcquisition(acquire) and
  acquiredVar = getAcquiredVariable(acquire) and
  hasLeakingReturn(acquire, acquiredVar) and
  not isInFixedFunction(acquire)
select acquire,
  "Call to " + acquire.getTarget().getName() +
    " stores result in '" + acquiredVar.getName() +
    "' but kfree() is not called on every return path, causing a memory leak"
