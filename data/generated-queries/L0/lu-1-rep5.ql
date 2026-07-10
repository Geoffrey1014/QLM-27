/**
 * @name Missing sctp_association_free after sctp_unpack_cookie (memory leak)
 * @description Detects sctp_association objects returned by sctp_unpack_cookie
 *              that are stored in a local variable but never released with
 *              sctp_association_free on that same variable within the
 *              enclosing function. Based on the pattern of the b6631c6031c7
 *              fix ("sctp: Fix memory leak in sctp_sf_do_5_2_4_dupcook").
 * @kind problem
 * @problem.severity warning
 * @id qlm/l0-lu1-sctp-unpack-cookie-leak
 */
import cpp

predicate isAcquireCall(FunctionCall fc) {
  fc.getTarget().getName() = "sctp_unpack_cookie"
}

from FunctionCall acquire, Function enclosing, Variable v
where isAcquireCall(acquire)
  and enclosing = acquire.getEnclosingFunction()
  and exists(AssignExpr ae |
    ae.getRValue() = acquire and
    ae.getLValue() = v.getAnAccess()
  )
  and not exists(FunctionCall release |
    release.getTarget().getName() = "sctp_association_free" and
    release.getEnclosingFunction() = enclosing and
    release.getAnArgument() = v.getAnAccess()
  )
select acquire,
  "sctp_unpack_cookie result assigned to '" + v.getName() +
  "' may be leaked in function '" + enclosing.getName() +
  "' (no sctp_association_free on this variable)."
