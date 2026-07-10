/**
 * @name C3 generated query for lu-1 / fix b6631c6031c7
 * @description Missing sctp_association_free after sctp_unpack_cookie allocation
 *              on the security_sctp_assoc_request error path (CWE-401)
 * @kind problem
 * @problem.severity warning
 * @id cpp/rq3/c3/lu-1-rep4
 */

import cpp

predicate isAssocAcquisition(FunctionCall fc) {
  fc.getTarget().getName() in [
    "sctp_unpack_cookie",
    "sctp_association_new",
    "sctp_make_temp_asoc"
  ]
}

predicate isAssocFree(FunctionCall fc) {
  fc.getTarget().getName() = "sctp_association_free"
}

Variable getAcquiredVariable(FunctionCall acquire) {
  exists(AssignExpr assign |
    assign.getRValue() = acquire and
    result = assign.getLValue().(VariableAccess).getTarget()
  )
}

predicate hasMatchingAssocFree(FunctionCall acquire, Variable v) {
  exists(FunctionCall freeCall |
    isAssocFree(freeCall) and
    freeCall.getEnclosingFunction() = acquire.getEnclosingFunction() and
    exists(VariableAccess va |
      va = freeCall.getArgument(0) and
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
  isAssocAcquisition(acquire) and
  acquiredVar = getAcquiredVariable(acquire) and
  hasNullCheck(acquire, acquiredVar) and
  not hasMatchingAssocFree(acquire, acquiredVar) and
  not isInFixedFunction(acquire)
select acquire,
  "Call to " + acquire.getTarget().getName() +
    " stores result in '" + acquiredVar.getName() +
    "' but sctp_association_free() is never called, causing an sctp_association memory leak"
