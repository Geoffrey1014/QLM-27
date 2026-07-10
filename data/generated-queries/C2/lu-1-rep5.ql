/**
 * @name  rq3-c2-lu-1-rep5
 * @id    cpp/rq3/c2/lu-1-rep5
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detect missing sctp_association_free on error paths after
 *              an SCTP association is allocated and a security check fails.
 */

import cpp

/** Holds if `v` is assigned the result of an SCTP association allocator. */
predicate allocates_assoc(LocalVariable v, Expr alloc) {
  exists(FunctionCall fc |
    fc = alloc and
    fc.getTarget().getName().regexpMatch("sctp_(make_temp_asoc|association_new|sf_do_5_1B_init|sf_do_unexpected_init)") and
    (
      v.getInitializer().getExpr() = fc
      or
      exists(AssignExpr ae | ae.getLValue() = v.getAnAccess() and ae.getRValue() = fc)
    )
  )
}

/** Holds if `call` is a security check call that returns non-zero on failure. */
predicate is_security_check(FunctionCall call) {
  call.getTarget().getName().matches("security_%")
}

/** Holds if `ret` is the failure-path return guarded by the security check. */
predicate failure_return_after_check(FunctionCall sec, ReturnStmt ret) {
  exists(IfStmt ifs |
    ifs.getCondition().getAChild*() = sec and
    ret.getParent*() = ifs.getThen()
  )
}

/** Holds if `freeCall` frees the variable `v` via sctp_association_free. */
predicate frees_assoc(FunctionCall freeCall, LocalVariable v) {
  freeCall.getTarget().getName() = "sctp_association_free" and
  freeCall.getArgument(0) = v.getAnAccess()
}

/** Holds if there is no free of `v` before `ret` inside the same function. */
predicate no_free_before_return(LocalVariable v, ReturnStmt ret) {
  not exists(FunctionCall freeCall |
    frees_assoc(freeCall, v) and
    freeCall.getEnclosingFunction() = ret.getEnclosingFunction() and
    freeCall.getLocation().getStartLine() < ret.getLocation().getStartLine()
  )
}

from LocalVariable v, Expr alloc, FunctionCall sec, ReturnStmt ret
where
  allocates_assoc(v, alloc) and
  is_security_check(sec) and
  failure_return_after_check(sec, ret) and
  sec.getEnclosingFunction() = alloc.getEnclosingFunction() and
  ret.getEnclosingFunction() = alloc.getEnclosingFunction() and
  no_free_before_return(v, ret)
select ret,
  "Possible leak of SCTP association allocated at $@ when security check $@ fails.",
  alloc, "allocation", sec, "security check"
