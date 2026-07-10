/**
 * @name Memory leak: sctp_unpack_cookie result not freed on error path
 * @description Detects functions where sctp_unpack_cookie() acquires a
 *              new_asoc value into a local variable that is not released via
 *              sctp_association_free() on some path.
 * @kind problem
 * @problem.severity warning
 * @id qlm-lu-1-rep3-l1-leak-sctp-unpack-cookie
 */
import cpp

predicate acquiresNewAsoc(FunctionCall acquire, LocalVariable v) {
  acquire.getTarget().getName() = "sctp_unpack_cookie" and
  (
    v.getInitializer().getExpr() = acquire
    or
    exists(AssignExpr a |
      a.getRValue() = acquire and
      a.getLValue() = v.getAnAccess()
    )
  )
}

predicate notFreedInFunction(FunctionCall acquire, LocalVariable v) {
  acquiresNewAsoc(acquire, v) and
  not exists(FunctionCall free |
    free.getEnclosingFunction() = acquire.getEnclosingFunction() and
    free.getTarget().getName() = "sctp_association_free" and
    free.getAnArgument() = v.getAnAccess()
  )
}

from FunctionCall acquire, LocalVariable v
where notFreedInFunction(acquire, v)
select acquire,
  "Possible memory leak: sctp_unpack_cookie result stored in " + v.getName() +
    " is not released by sctp_association_free on all paths"
