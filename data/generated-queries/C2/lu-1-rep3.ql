/**
 * @name  rq3-c2-lu-1-rep3
 * @id    cpp/rq3/c2/lu-1-rep3
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects leak of sctp_association on error-discard paths
 *              (pattern from commit b6631c6031c7).
 */
import cpp

/** Holds if `v` is a local variable initialized from an SCTP association allocator. */
predicate allocates_assoc(LocalVariable v, FunctionCall alloc) {
  alloc = v.getInitializer().getExpr() and
  alloc.getTarget().getName().regexpMatch("sctp_(make_temp_asoc|association_new|assoc_new)")
}

/** Holds if `fc` is a call to sctp_association_free whose first argument is `v`. */
predicate frees_assoc(FunctionCall fc, LocalVariable v) {
  fc.getTarget().getName() = "sctp_association_free" and
  fc.getArgument(0) = v.getAnAccess()
}

/** Holds if `ret` returns the result of an SCTP discard/error helper. */
predicate error_discard_return(ReturnStmt ret, FunctionCall discardCall) {
  discardCall = ret.getExpr() and
  discardCall.getTarget().getName().regexpMatch("sctp_sf_(pdiscard|violation.*|nomem.*)")
}

/** Holds if there is a CFG path from `alloc` to `ret` that does not go through
 *  a call freeing `v`. */
predicate leaks_assoc_on_error(LocalVariable v, FunctionCall alloc, ReturnStmt ret, FunctionCall discardCall) {
  allocates_assoc(v, alloc) and
  error_discard_return(ret, discardCall) and
  alloc.getEnclosingFunction() = ret.getEnclosingFunction() and
  ret = alloc.getASuccessor+() and
  not exists(FunctionCall freeFc |
    frees_assoc(freeFc, v) and
    freeFc = alloc.getASuccessor+() and
    ret = freeFc.getASuccessor+()
  )
}

from LocalVariable v, FunctionCall alloc, ReturnStmt ret, FunctionCall discardCall
where leaks_assoc_on_error(v, alloc, ret, discardCall)
select ret,
  "Potential leak of sctp_association '" + v.getName() +
  "' allocated at $@ on error-discard path returning $@.",
  alloc, alloc.toString(), discardCall, discardCall.getTarget().getName()
