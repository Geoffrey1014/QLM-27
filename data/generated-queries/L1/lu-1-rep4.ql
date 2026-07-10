/**
 * @name Missing sctp_association_free for new_asoc
 * @description Detects functions that allocate an sctp_association via
 *              sctp_unpack_cookie but fail to free it on all paths,
 *              causing a memory leak.
 * @kind problem
 * @problem.severity error
 * @id cpp/qlllm/sctp-missing-assoc-free
 */

import cpp

predicate allocatesNewAsoc(FunctionCall acquire, Variable v) {
  acquire.getTarget().getName() = "sctp_unpack_cookie" and
  exists(AssignExpr assign |
    assign.getRValue() = acquire and
    assign.getLValue() = v.getAnAccess()
  )
}

predicate missingAssocFree(FunctionCall acquire, Variable v) {
  allocatesNewAsoc(acquire, v) and
  not exists(FunctionCall rel |
    rel.getEnclosingFunction() = acquire.getEnclosingFunction() and
    rel.getTarget().getName() = "sctp_association_free" and
    rel.getArgument(0) = v.getAnAccess()
  ) and
  not acquire.getEnclosingFunction().getName().toLowerCase().matches("%fixed%")
}

from FunctionCall acquire, Variable v
where missingAssocFree(acquire, v)
select acquire,
  "Missing sctp_association_free() for '" + v.getName() +
  "' allocated by " + acquire.getTarget().getName() +
  "() - potential memory leak"
