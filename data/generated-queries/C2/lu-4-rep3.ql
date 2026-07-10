/**
 * @name  rq3-c2-lu-4-rep3
 * @id    cpp/rq3/c2/lu-4-rep3
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 */
import cpp

/** Holds if `call` is a call to the resource-acquiring target API. */
predicate isTargetAcquireCall(FunctionCall call) {
  call.getTarget().hasName("platform_device_alloc")
}

/** Holds if `call` releases the resource via the post-operation. */
predicate isPostReleaseCall(FunctionCall call) {
  call.getTarget().hasName("platform_device_put")
}

/** Holds if `v` is the critical variable that holds the acquired resource
 *  (i.e. a variable assigned the result of an acquire call). */
predicate holdsAcquiredResource(Variable v, FunctionCall acquire) {
  isTargetAcquireCall(acquire) and
  (
    // direct assignment:  v = platform_device_alloc(...)
    exists(AssignExpr a |
      a.getRValue() = acquire and
      a.getLValue() = v.getAnAccess())
    or
    // field/pointer expression target also fine: dwc->dwc3 = platform_device_alloc(...)
    // handle generally via any access of v reachable from the assignment lhs
    exists(Assignment a |
      a.getRValue() = acquire and
      a.getLValue().(VariableAccess).getTarget() = v)
  )
}

/** Holds if function `f` contains an acquire of resource into variable `v`
 *  and there exists an error-path return after the acquire that is NOT
 *  preceded by a post-release call on `v`. */
predicate missingReleaseOnErrorPath(Function f, FunctionCall acquire, ReturnStmt ret) {
  exists(Variable v |
    holdsAcquiredResource(v, acquire) and
    acquire.getEnclosingFunction() = f and
    ret.getEnclosingFunction() = f and
    // return happens after acquire in source order (cheap proxy)
    ret.getLocation().getStartLine() > acquire.getLocation().getStartLine() and
    // return value is a non-zero error code (or any expr - kept simple)
    exists(ret.getExpr()) and
    // no post-release call on a member/field expression between acquire and return
    not exists(FunctionCall release |
      isPostReleaseCall(release) and
      release.getEnclosingFunction() = f and
      release.getLocation().getStartLine() > acquire.getLocation().getStartLine() and
      release.getLocation().getStartLine() < ret.getLocation().getStartLine()
    )
  )
}

from Function f, FunctionCall acquire, ReturnStmt ret
where missingReleaseOnErrorPath(f, acquire, ret)
select ret,
  "Possible missing platform_device_put on error path after platform_device_alloc in $@.",
  f, f.getName()
