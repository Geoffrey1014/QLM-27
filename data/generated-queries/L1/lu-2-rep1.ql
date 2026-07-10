/**
 * @name L1 generated query for lu-2 / fix 2289adbfa559
 * @description Missing kfree after kmalloc on an error return path —
 *              memory leak in the four-features-Lu pattern (CWE-401).
 * @kind problem
 * @problem.severity warning
 * @id cpp/rq3/l1/lu-2-rep1
 */

import cpp

predicate isAcquisition(FunctionCall fc) {
  fc.getTarget().getName() in ["kmalloc", "kzalloc", "kcalloc"]
}

predicate isReleaseCall(FunctionCall fc) {
  fc.getTarget().getName() in ["kfree", "kvfree", "kzfree"]
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
    "' but kfree() is never called, causing a possible memory leak"
