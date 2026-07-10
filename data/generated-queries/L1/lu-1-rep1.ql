/**
 * @name L1 generated query for lu-1 / fix b6631c6031c7
 * @description Missing sctp_association_free after sctp_unpack_cookie - memory leak (CWE-401)
 * @kind problem
 * @problem.severity warning
 * @id cpp/rq3/l1/lu-1-rep1
 */

import cpp

predicate allocatesResource(FunctionCall acquire, Variable v) {
  acquire.getTarget().getName() = "sctp_unpack_cookie" and
  exists(AssignExpr assign |
    assign.getRValue() = acquire and
    v = assign.getLValue().(VariableAccess).getTarget()
  )
}

predicate hasMissingRelease(FunctionCall acquire, Variable v) {
  allocatesResource(acquire, v) and
  not exists(FunctionCall rel |
    rel.getEnclosingFunction() = acquire.getEnclosingFunction() and
    rel.getTarget().getName() = "sctp_association_free" and
    exists(VariableAccess va |
      va = rel.getArgument(0) and va.getTarget() = v
    )
  ) and
  not acquire.getEnclosingFunction().getName().toLowerCase().matches("%fixed%")
}

from FunctionCall acquire, Variable v
where hasMissingRelease(acquire, v)
select acquire,
  "Missing sctp_association_free() for variable '" + v.getName() +
  "' allocated by " + acquire.getTarget().getName() +
  "() - potential memory leak"
