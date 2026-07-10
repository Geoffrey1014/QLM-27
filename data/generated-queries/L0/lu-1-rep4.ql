/**
 * @name Missing sctp_association_free after sctp_unpack_cookie (sctp_association memory leak)
 * @description Detects sctp_association pointers acquired via sctp_unpack_cookie
 *              (or peer allocators) that are null-checked and used further in the
 *              enclosing function without a matching sctp_association_free on the
 *              same variable — leaking new_asoc on error paths such as the
 *              security_sctp_assoc_request rejection in sctp_sf_do_5_2_4_dupcook.
 * @kind problem
 * @problem.severity warning
 * @id qlm/l0-lu1-sctp-assoc-leak
 */
import cpp

predicate isAssocAcquisition(FunctionCall fc) {
  fc.getTarget().getName() in [
    "sctp_unpack_cookie",
    "sctp_association_new",
    "sctp_make_temp_asoc"
  ]
}

from FunctionCall acquire, Function enclosing, Variable v
where isAssocAcquisition(acquire)
  and enclosing = acquire.getEnclosingFunction()
  and exists(AssignExpr ae |
    ae.getRValue() = acquire and
    ae.getLValue() = v.getAnAccess()
  )
  and exists(IfStmt ifStmt, VariableAccess va |
    ifStmt.getEnclosingFunction() = enclosing and
    va.getTarget() = v and
    ifStmt.getCondition().getAChild*() = va
  )
  and not exists(FunctionCall release |
    release.getTarget().getName() = "sctp_association_free" and
    release.getEnclosingFunction() = enclosing and
    release.getAnArgument() = v.getAnAccess()
  )
  and not enclosing.getName().toLowerCase().matches("%fixed%")
select acquire,
  "sctp_association acquired via " + acquire.getTarget().getName() +
  " and assigned to '" + v.getName() +
  "' may be leaked in function '" + enclosing.getName() +
  "' (no sctp_association_free on this variable)."
