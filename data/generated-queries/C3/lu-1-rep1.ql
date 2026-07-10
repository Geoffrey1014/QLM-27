/**
 * @name C3 generated query for lu-1 / fix b6631c6031c7
 * @description Missing sctp_association_free after sctp_unpack_cookie — memory leak (CWE-401)
 * @kind problem
 * @problem.severity warning
 * @id cpp/rq3/c3/lu-1-rep1
 */

import cpp

predicate isAcquisition(FunctionCall fc) {
  fc.getTarget().getName() in [
    "sctp_unpack_cookie",
    "sctp_association_new",
    "sctp_make_assoc"
  ]
}

predicate isReleaseCall(FunctionCall fc) {
  fc.getTarget().getName() in [
    "sctp_association_free",
    "sctp_association_put"
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
    "' but sctp_association_free() is never called, causing a memory leak"
