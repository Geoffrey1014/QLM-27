/**
 * @name  rq3-c2-lin-4-rep1
 * @id    cpp/rq3/c2/lin-4-rep1
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detect refcount leaks where of_parse_phandle()'s returned
 *              device_node is not released by of_node_put() on every
 *              return path.
 */

import cpp

/** Holds if `call` acquires a device_node via of_parse_phandle (or sibling acquirers). */
predicate isAcquireCall(FunctionCall call) {
  call.getTarget().getName() = "of_parse_phandle"
}

/** Holds if `v` is the local variable that receives the acquired node from `call`. */
predicate acquiredInto(FunctionCall call, LocalVariable v) {
  isAcquireCall(call) and
  (
    v.getInitializer().getExpr() = call
    or
    exists(AssignExpr a |
      a.getRValue() = call and
      a.getLValue() = v.getAnAccess()
    )
  )
}

/** Holds if `call` is a release of the device_node held by `v` (of_node_put(v)). */
predicate isReleaseCall(FunctionCall call, LocalVariable v) {
  call.getTarget().getName() = "of_node_put" and
  call.getArgument(0) = v.getAnAccess()
}

/** Holds if `ret` is a return statement reachable after `acq` without any release of `v`. */
predicate returnsWithoutRelease(FunctionCall acq, LocalVariable v, ReturnStmt ret) {
  acquiredInto(acq, v) and
  ret.getEnclosingFunction() = acq.getEnclosingFunction() and
  acq.getASuccessor+() = ret and
  not exists(FunctionCall rel |
    isReleaseCall(rel, v) and
    acq.getASuccessor+() = rel and
    rel.getASuccessor+() = ret
  )
}

/** Holds if function `f` contains the leak: acquire reaches a return without release. */
predicate hasRefcountLeak(Function f, FunctionCall acq, LocalVariable v, ReturnStmt leakRet) {
  acq.getEnclosingFunction() = f and
  acquiredInto(acq, v) and
  returnsWithoutRelease(acq, v, leakRet)
}

from Function f, FunctionCall acq, LocalVariable v, ReturnStmt leakRet
where hasRefcountLeak(f, acq, v, leakRet)
select leakRet,
  "Possible refcount leak: device_node acquired by of_parse_phandle at $@ via variable '" +
    v.getName() + "' is not released by of_node_put() on this return path.",
  acq, acq.toString()
