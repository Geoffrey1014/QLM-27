/**
 * @name  rq3-c2-lu-1-rep1
 * @id    cpp/rq3/c2/lu-1-rep1
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects resource-allocation pointers (e.g. sctp_unpack_cookie)
 *              that may be leaked on an early-return error path because the
 *              required release operation (e.g. sctp_association_free) was
 *              not invoked before returning.
 */

import cpp

/* P1: identify allocator-like calls whose return value is assigned to a local
 *     pointer variable. Matches the four-features Target API role. */
predicate allocates_resource(FunctionCall alloc, LocalVariable v) {
  exists(Function f |
    f = alloc.getTarget() and
    (
      f.getName() = "sctp_unpack_cookie" or
      f.getName().matches("%_alloc%") or
      f.getName().matches("%_new") or
      f.getName().matches("%_create%") or
      f.getName().matches("%kmalloc%") or
      f.getName().matches("%kzalloc%")
    )
  ) and
  v.getType() instanceof PointerType and
  (
    exists(AssignExpr a |
      a.getRValue() = alloc and a.getLValue() = v.getAnAccess()
    )
    or
    v.getInitializer().getExpr() = alloc
  )
}

/* P2: identify release/free-like calls that take v as a parameter. */
predicate is_release_call(FunctionCall rel, LocalVariable v) {
  exists(Function f |
    f = rel.getTarget() and
    (
      f.getName() = "sctp_association_free" or
      f.getName().matches("%_free%") or
      f.getName().matches("%_release%") or
      f.getName().matches("%_put") or
      f.getName().matches("%kfree%")
    )
  ) and
  rel.getAnArgument() = v.getAnAccess()
}

/* P3: a return statement that is control-flow-reachable from `alloc` and is
 *     guarded by some IfStmt's then-branch (the error-path shape). */
predicate guarded_early_return(FunctionCall alloc, ReturnStmt ret, LocalVariable v) {
  alloc.getEnclosingFunction() = ret.getEnclosingFunction() and
  allocates_resource(alloc, v) and
  exists(IfStmt ifs |
    ifs.getEnclosingFunction() = ret.getEnclosingFunction() and
    ret.getParent*() = ifs.getThen() and
    /* the if-condition is reachable after the allocation: same function and
     * the if statement textually follows the allocation. */
    ifs.getLocation().getStartLine() > alloc.getLocation().getStartLine()
  )
}

/* P4: no release call for v occurs on the path from the allocation to the
 *     early return. Approximated intra-procedurally: there is no release_call
 *     of v in the same function whose location is between the allocation and
 *     the return. */
predicate no_release_before_return(FunctionCall alloc, ReturnStmt ret, LocalVariable v) {
  guarded_early_return(alloc, ret, v) and
  not exists(FunctionCall rel |
    is_release_call(rel, v) and
    rel.getEnclosingFunction() = alloc.getEnclosingFunction() and
    rel.getLocation().getStartLine() >= alloc.getLocation().getStartLine() and
    rel.getLocation().getStartLine() <= ret.getLocation().getStartLine()
  )
}

from FunctionCall alloc, ReturnStmt ret, LocalVariable v
where
  allocates_resource(alloc, v) and
  guarded_early_return(alloc, ret, v) and
  no_release_before_return(alloc, ret, v)
select ret,
  "Possible leak of '" + v.getName() + "' allocated by '" +
    alloc.getTarget().getName() + "' on this early-return path."
