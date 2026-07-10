/**
 * @name Missing sctp_association_free after sctp_unpack_cookie
 * @description Detects functions that call sctp_unpack_cookie (which
 *              allocates a new association) but never call
 *              sctp_association_free on any path, leaking the resource
 *              on error paths.
 * @kind problem
 * @problem.severity warning
 * @id qlm/lu-1-rep5-missing-sctp-association-free
 */

import cpp

predicate isAcquireCall(FunctionCall fc) {
  fc.getTarget().getName() = "sctp_unpack_cookie"
}

predicate isReleaseCall(FunctionCall fc, Expr arg) {
  fc.getTarget().getName() = "sctp_association_free" and arg = fc.getArgument(0)
}

predicate missingReleaseAfterAcquire(FunctionCall acquire, Function f) {
  isAcquireCall(acquire) and
  f = acquire.getEnclosingFunction() and
  not exists(FunctionCall rel | rel.getEnclosingFunction() = f and isReleaseCall(rel, _))
}

from FunctionCall acquire, Function f
where missingReleaseAfterAcquire(acquire, f)
select acquire, "Missing sctp_association_free in " + f.getName()
