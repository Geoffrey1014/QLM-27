/**
 * @name  rq3-c2-lin-5-rep4
 * @id    cpp/rq3/c2/lin-5-rep4
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects missing put_device() after of_find_device_by_node()
 *              on early-return error paths (refcount leak pattern).
 */
import cpp

/* P1: identify the resource acquisition call site */
predicate acquiresDeviceRef(FunctionCall acq) {
  acq.getTarget().getName() = "of_find_device_by_node"
}

/* P2: the variable that captures the acquired reference */
predicate holdsAcquiredDevice(Variable v, FunctionCall acq) {
  acquiresDeviceRef(acq) and
  (
    exists(AssignExpr a |
      a.getRValue() = acq and
      a.getLValue() = v.getAnAccess()
    )
    or
    exists(Initializer ini |
      ini.getExpr() = acq and
      ini.getDeclaration() = v
    )
  )
}

/* P3: a call put_device(&v->dev) that releases the reference for v */
predicate releasesDeviceRef(FunctionCall rel, Variable v) {
  rel.getTarget().getName() = "put_device" and
  exists(AddressOfExpr ao, FieldAccess fa |
    ao = rel.getArgument(0) and
    fa = ao.getOperand() and
    fa.getTarget().getName() = "dev" and
    fa.getQualifier() = v.getAnAccess()
  )
}

/* P4: a return statement reachable from the acquisition (in same function)
 *     that does NOT have an intervening release on its path. We approximate
 *     "missing release on path" by: there exists a return stmt after the
 *     acquisition in source order, and the enclosing function contains no
 *     release call for v before that return. */
predicate leakingReturn(ReturnStmt ret, FunctionCall acq, Variable v) {
  holdsAcquiredDevice(v, acq) and
  ret.getEnclosingFunction() = acq.getEnclosingFunction() and
  acq.getLocation().getStartLine() < ret.getLocation().getStartLine() and
  not exists(FunctionCall rel |
    releasesDeviceRef(rel, v) and
    rel.getEnclosingFunction() = acq.getEnclosingFunction() and
    rel.getLocation().getStartLine() < ret.getLocation().getStartLine()
  )
}

from FunctionCall acq, Variable v, ReturnStmt ret
where
  acquiresDeviceRef(acq) and
  holdsAcquiredDevice(v, acq) and
  leakingReturn(ret, acq, v)
select ret,
  "Possible refcount leak: " + v.getName() +
  " acquired via of_find_device_by_node() is not released by put_device() before this return."
