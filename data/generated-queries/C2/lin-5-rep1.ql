/**
 * @name  rq3-c2-lin-5-rep1
 * @id    cpp/rq3/c2/lin-5-rep1
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detect missing put_device() after of_find_device_by_node() acquires
 *              a reference, on early-return paths.
 */

import cpp

/** A call to the target API that acquires a refcounted platform_device. */
predicate isAcquireCall(FunctionCall acq) {
  acq.getTarget().hasName("of_find_device_by_node")
}

/** The variable that stores the acquired device pointer. */
predicate acquiresIntoVar(FunctionCall acq, Variable v) {
  isAcquireCall(acq) and
  exists(AssignExpr a |
    a.getRValue() = acq and
    a.getLValue() = v.getAnAccess()
  )
}

/** A call that releases the reference (the required post-operation). */
predicate isReleaseCall(FunctionCall rel, Variable v) {
  rel.getTarget().hasName("put_device") and
  exists(AddressOfExpr aof, FieldAccess fa |
    rel.getArgument(0) = aof and
    aof.getOperand() = fa and
    fa.getQualifier() = v.getAnAccess() and
    fa.getTarget().hasName("dev")
  )
}

/** A return statement that is reached *after* the acquire (control-flow successor)
 *  and does not have a release of v on the path between acquire and the return. */
predicate returnAfterAcquireWithoutRelease(FunctionCall acq, Variable v, ReturnStmt ret) {
  acquiresIntoVar(acq, v) and
  acq.getEnclosingFunction() = ret.getEnclosingFunction() and
  acq.getASuccessor+() = ret and
  not exists(FunctionCall rel |
    isReleaseCall(rel, v) and
    acq.getASuccessor+() = rel and
    rel.getASuccessor+() = ret
  )
}

/** The acquire call is guarded by a non-null check on v (typical pattern:
 *  `dev = of_find_device_by_node(...); if (dev) { ... }`) — used to limit FPs
 *  to the legitimate "acquired" branch. */
predicate insideAcquiredBranch(FunctionCall acq, Variable v, ReturnStmt ret) {
  returnAfterAcquireWithoutRelease(acq, v, ret) and
  exists(IfStmt ifs |
    ifs.getEnclosingFunction() = acq.getEnclosingFunction() and
    ifs.getCondition().getAChild*() = v.getAnAccess() and
    acq.getASuccessor+() = ifs.getCondition() and
    ifs.getThen().getASuccessor*() = ret
  )
}

from FunctionCall acq, Variable v, ReturnStmt ret
where
  insideAcquiredBranch(acq, v, ret)
select ret,
  "Missing put_device(&" + v.getName() + "->dev) on early-return path after of_find_device_by_node()."
