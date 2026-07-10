/**
 * @name Memory leak: sctp_unpack_cookie result not freed on error path
 * @description Detects functions where sctp_unpack_cookie() acquires a
 *              new_asoc value that is not released via
 *              sctp_association_free() on all paths.
 * @kind problem
 * @problem.severity warning
 * @id qlm-lu-1-rep3-leak-sctp-unpack-cookie
 */
import cpp

predicate leaksNewAsocOnErrorReturn(FunctionCall acquire, ReturnStmt ret) {
  acquire.getTarget().getName() = "sctp_unpack_cookie" and
  exists(Function f, LocalVariable v |
    acquire.getEnclosingFunction() = f and
    ret.getEnclosingFunction() = f and
    (
      v.getInitializer().getExpr() = acquire
      or
      exists(AssignExpr a |
        a.getRValue() = acquire and
        a.getLValue() = v.getAnAccess()
      )
    ) and
    not exists(FunctionCall free |
      free.getEnclosingFunction() = f and
      free.getTarget().getName() = "sctp_association_free" and
      free.getAnArgument() = v.getAnAccess()
    )
  )
}

from FunctionCall acquire, ReturnStmt ret
where leaksNewAsocOnErrorReturn(acquire, ret)
select acquire, "Possible memory leak: sctp_unpack_cookie result not freed on function-wide return paths"
