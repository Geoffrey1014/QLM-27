/**
 * @name  rq3-c2-lin-5-rep5
 * @id    cpp/rq3/c2/lin-5-rep5
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects missing put_device() after of_find_device_by_node().
 */

import cpp

/** A call to the resource-acquiring API. */
predicate isAcquireCall(FunctionCall fc) {
  fc.getTarget().hasName("of_find_device_by_node")
}

/** A call to the resource-releasing API. */
predicate isReleaseCall(FunctionCall fc) {
  fc.getTarget().hasName("put_device")
}

/** The local variable that receives the acquired resource. */
predicate acquiresInto(FunctionCall acq, LocalVariable v) {
  isAcquireCall(acq) and
  exists(Expr init |
    (init = v.getInitializer().getExpr() or
     exists(AssignExpr ae | ae.getLValue() = v.getAnAccess() and ae.getRValue() = init)) and
    init = acq
  )
}

/** A release call that targets variable v (either v or &v->dev). */
predicate releasesVar(FunctionCall rel, LocalVariable v) {
  isReleaseCall(rel) and
  exists(Expr arg | arg = rel.getArgument(0) |
    arg = v.getAnAccess() or
    arg.(AddressOfExpr).getOperand().(FieldAccess).getQualifier() = v.getAnAccess() or
    arg.(AddressOfExpr).getOperand().(PointerFieldAccess).getQualifier() = v.getAnAccess()
  )
}

/** A return statement that occurs in the same function as the acquire,
 *  after the acquire textually, and is not preceded by a release of v. */
predicate leakyReturn(FunctionCall acq, LocalVariable v, ReturnStmt ret) {
  acquiresInto(acq, v) and
  ret.getEnclosingFunction() = acq.getEnclosingFunction() and
  ret.getLocation().getStartLine() > acq.getLocation().getStartLine() and
  not exists(FunctionCall rel |
    releasesVar(rel, v) and
    rel.getEnclosingFunction() = acq.getEnclosingFunction() and
    rel.getLocation().getStartLine() > acq.getLocation().getStartLine() and
    rel.getLocation().getStartLine() < ret.getLocation().getStartLine()
  )
}

from FunctionCall acq, LocalVariable v, ReturnStmt ret
where leakyReturn(acq, v, ret)
select ret,
  "Possible refcount leak: " + v.getName() +
  " acquired via of_find_device_by_node at line " + acq.getLocation().getStartLine() +
  " is not released by put_device before this return."
