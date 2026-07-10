/**
 * @name Missing resource release on error path after allocation
 * @description Detects functions that allocate a resource via an
 *              alloc-style API, store the result into a pointer
 *              field/variable, but then fail to invoke a matching
 *              release function on an error path that returns directly
 *              instead of going to a cleanup label.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-lu-4
 */

import cpp

/**
 * Pairs of (acquire, release) function names that follow the
 * platform_device_alloc / platform_device_put style of resource
 * lifecycle. Kept generic so the query can fire on similar leaks
 * elsewhere in the kernel.
 */
predicate acquireReleasePair(string acquire, string release) {
  acquire = "platform_device_alloc" and release = "platform_device_put"
  or
  acquire = "of_node_get" and release = "of_node_put"
  or
  acquire = "device_node_get" and release = "of_node_put"
  or
  acquire = "kobject_get" and release = "kobject_put"
  or
  acquire = "get_device" and release = "put_device"
  or
  acquire = "usb_get_dev" and release = "usb_put_dev"
}

/** A call that acquires a resource which must later be released. */
class AcquireCall extends FunctionCall {
  string releaseName;

  AcquireCall() {
    exists(string acq |
      acquireReleasePair(acq, releaseName) and
      this.getTarget().getName() = acq
    )
  }

  string getReleaseName() { result = releaseName }
}

/**
 * A return statement that returns a (probably error) integer
 * expression — i.e. one whose value is not a literal 0/1 success
 * sentinel. We use it as the locus that "early-returns on error
 * without releasing".
 */
class ErrorReturn extends ReturnStmt {
  ErrorReturn() {
    exists(Expr e | e = this.getExpr() |
      // returning a previously-assigned ret-style variable
      e instanceof VariableAccess
      or
      // returning a negative integer literal directly
      e.getValue().toInt() < 0
      or
      // returning result of unary minus
      e instanceof UnaryMinusExpr
    )
  }
}

/**
 * Is there a release call (matching `releaseName`) reachable on
 * the successor side of this control-flow node, before the
 * function exits via the given return?
 */
predicate releaseReachableBefore(ControlFlowNode start, ReturnStmt ret, string releaseName) {
  exists(FunctionCall rc |
    rc.getTarget().getName() = releaseName and
    start.getASuccessor*() = rc and
    rc.getASuccessor*() = ret
  )
}

from
  Function f, AcquireCall ac, ErrorReturn ret, IfStmt guard, ControlFlowNode acNode,
  string releaseName
where
  // acquire is in the function under analysis
  ac.getEnclosingFunction() = f and
  ret.getEnclosingFunction() = f and
  releaseName = ac.getReleaseName() and
  acNode = ac and
  // the return happens after the acquire (in CFG order)
  acNode.getASuccessor+() = ret and
  // the return sits inside an if-guard whose condition tests the
  // result of a subsequent call (the post-acquire add/setup step
  // that may fail) — i.e. a true error path
  guard.getEnclosingFunction() = f and
  acNode.getASuccessor+() = guard and
  guard.getThen().getAChild*() = ret and
  // exclude the alloc-null check itself: there is at least one
  // intervening non-null function call between acquire and the
  // if-guard, distinguishing "alloc-failed bail" from
  // "post-acquire setup failed bail"
  exists(FunctionCall mid |
    mid.getEnclosingFunction() = f and
    mid != ac and
    acNode.getASuccessor+() = mid and
    mid.getASuccessor+() = guard
  ) and
  // no release on the path from the acquire through this return
  not releaseReachableBefore(acNode, ret, releaseName) and
  // and somewhere else in the same function the release IS used
  // (so we know the author meant to release it, just missed this
  // path).  This anchors the FP rate.
  exists(FunctionCall rc |
    rc.getEnclosingFunction() = f and
    rc.getTarget().getName() = releaseName
  )
select ret,
  "Possible resource leak: '" + ac.getTarget().getName() +
    "' acquired here is not released via '" + releaseName +
    "' on this error-return path (other paths in $@ do release it).", f, f.getName()
