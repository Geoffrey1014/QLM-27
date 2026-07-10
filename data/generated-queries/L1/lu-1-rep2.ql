/**
 * @name Potential leak of sctp_unpack_cookie result
 * @description Detects functions that call sctp_unpack_cookie to
 *              acquire an sctp_association without releasing it via
 *              sctp_association_free anywhere in the same function.
 *              Models the bug pattern fixed by b6631c6031c7
 *              ("sctp: Fix memory leak in sctp_sf_do_5_2_4_dupcook").
 * @kind problem
 * @problem.severity warning
 * @id qlm-l1-lu-1-rep2
 */

import cpp

predicate isAcquireCall(FunctionCall fc) {
  fc.getTarget().getName() = "sctp_unpack_cookie"
}

from FunctionCall acquire, Function enclosing
where
  isAcquireCall(acquire)
  and enclosing = acquire.getEnclosingFunction()
  and not exists(FunctionCall free |
    free.getEnclosingFunction() = enclosing
    and free.getTarget().getName() = "sctp_association_free"
  )
select acquire,
  "Potential leak: sctp_unpack_cookie result not released by sctp_association_free in "
  + enclosing.getName()
