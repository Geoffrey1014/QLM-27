/**
 * @name C3 generated query for lu-5 / fix 450c3d416683
 * @description Missing kfree after kstrdup — memory leak (CWE-401)
 * @kind problem
 * @problem.severity warning
 * @id cpp/rq3/c3/lu-5-rep1
 */

import cpp

predicate isAcquisition(FunctionCall fc) {
  fc.getTarget().getName() in [
    "kstrdup",
    "kstrdup_const",
    "kmemdup"
  ]
}

predicate isReleaseCall(FunctionCall fc) {
  fc.getTarget().getName() in [
    "kfree",
    "kfree_const",
    "kvfree"
  ]
}

Variable getAcquiredVariable(FunctionCall acquire) {
  exists(AssignExpr assign |
    assign.getRValue() = acquire and
    result = assign.getLValue().(VariableAccess).getTarget()
  )
}

predicate hasMatchingRelease(FunctionCall acquire, Variable v) {
  exists(FunctionCall rel |
    isReleaseCall(rel) and
    rel.getEnclosingFunction() = acquire.getEnclosingFunction() and
    exists(VariableAccess va |
      va = rel.getArgument(0) and
      va.getTarget() = v
    )
  )
}

predicate hasNullCheck(FunctionCall acquire, Variable v) {
  exists(IfStmt ifStmt, VariableAccess va |
    ifStmt.getEnclosingFunction() = acquire.getEnclosingFunction() and
    va.getTarget() = v and
    ifStmt.getCondition().getAChild*() = va
  )
}

predicate isInFixedFunction(FunctionCall fc) {
  fc.getEnclosingFunction().getName().toLowerCase().matches("%fixed%")
}

from FunctionCall acquire, Variable acquiredVar
where
  isAcquisition(acquire) and
  acquiredVar = getAcquiredVariable(acquire) and
  hasNullCheck(acquire, acquiredVar) and
  not hasMatchingRelease(acquire, acquiredVar) and
  not isInFixedFunction(acquire)
select acquire,
  "Call to " + acquire.getTarget().getName() +
    " stores result in '" + acquiredVar.getName() +
    "' but kfree() is never called on it, causing a memory leak"
