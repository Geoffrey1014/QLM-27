/**
 * @name  rq3-c2-lin-5-rep2
 * @id    cpp/rq3/c2/lin-5-rep2
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2. Detects refcount leaks
 *              where of_find_device_by_node acquires a device reference that is not
 *              released via put_device before function return.
 */

import cpp

predicate isTargetAcquireCall(FunctionCall fc) {
  fc.getTarget().getName() = "of_find_device_by_node"
}

predicate acquiredVariable(FunctionCall fc, Variable v) {
  isTargetAcquireCall(fc) and
  (
    exists(AssignExpr ae | ae.getRValue() = fc and ae.getLValue() = v.getAnAccess())
    or
    exists(Initializer init | init.getExpr() = fc and init.getDeclaration() = v)
  )
}

predicate isReleaseCallOn(FunctionCall rc, Variable v) {
  rc.getTarget().getName() = "put_device" and
  exists(AddressOfExpr ao | ao = rc.getArgument(0) and
    exists(FieldAccess fa | fa = ao.getOperand() and
      fa.getQualifier() = v.getAnAccess()))
}

predicate reachesReturnWithoutRelease(FunctionCall fc, Variable v, ReturnStmt r) {
  acquiredVariable(fc, v) and
  r.getEnclosingFunction() = fc.getEnclosingFunction() and
  // The acquire dominates the return path conceptually (we approximate by ordering)
  fc.getLocation().getStartLine() < r.getLocation().getStartLine() and
  // No release call on v lies between fc and r (intra-procedural approximation)
  not exists(FunctionCall rc |
    isReleaseCallOn(rc, v) and
    rc.getEnclosingFunction() = fc.getEnclosingFunction() and
    rc.getLocation().getStartLine() > fc.getLocation().getStartLine() and
    rc.getLocation().getStartLine() < r.getLocation().getStartLine()
  )
}

from FunctionCall fc, Variable v, ReturnStmt r
where acquiredVariable(fc, v) and reachesReturnWithoutRelease(fc, v, r)
select r, "Potential refcount leak: '" + v.getName() + "' acquired via of_find_device_by_node at $@ not released before return.", fc, fc.toString()
