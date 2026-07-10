/**
 * @name Missing put_device after of_find_device_by_node
 * @description of_find_device_by_node() returns a platform_device with its
 *              reference count incremented. The caller must drop the reference
 *              with put_device(&pdev->dev) on every path after the call (success
 *              or error), otherwise the device refcount is leaked. This query
 *              also generalizes to sibling APIs that return a refcounted
 *              struct device * (of_find_device_*, bus_find_device, etc.) where
 *              the corresponding release is put_device().
 * @kind problem
 * @problem.severity warning
 * @id cpp/missing-put-device-of-find
 * @tags reliability
 *       correctness
 *       resource-leak
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph

/**
 * A call to an OF/bus helper that returns a refcounted `struct platform_device *`
 * (or `struct device *`) and therefore obliges the caller to issue `put_device`
 * once the pointer is no longer used.
 */
class RefcountedDeviceAcquire extends FunctionCall {
  RefcountedDeviceAcquire() {
    exists(string n | n = this.getTarget().getName() |
      n = "of_find_device_by_node" or
      n = "of_find_device_by_phandle" or
      n = "bus_find_device" or
      n = "bus_find_device_by_name" or
      n = "bus_find_device_by_of_node" or
      n = "driver_find_device" or
      n = "driver_find_device_by_name" or
      n = "class_find_device"
    )
  }
}

/** A call to `put_device(...)`. */
class PutDeviceCall extends FunctionCall {
  PutDeviceCall() { this.getTarget().getName() = "put_device" }
}

/**
 * Holds if `e` is an expression whose value is (transitively) derived from the
 * call `acq` -- either `acq` itself, an assignment target of `acq`, or a field
 * access / address-of that ultimately roots at the local variable storing `acq`.
 */
predicate derivedFrom(Expr e, RefcountedDeviceAcquire acq, Function f) {
  e.getEnclosingFunction() = f and
  (
    e = acq
    or
    exists(Variable v |
      // v was assigned the result of acq
      (
        exists(AssignExpr a |
          a.getRValue() = acq and a.getLValue() = v.getAnAccess())
        or
        v.getInitializer().getExpr() = acq
      ) and
      // and e references v (e.g. &v->dev or v itself)
      (
        e = v.getAnAccess() or
        e.(AddressOfExpr).getOperand().(FieldAccess).getQualifier() = v.getAnAccess() or
        e.(FieldAccess).getQualifier() = v.getAnAccess() or
        e.(AddressOfExpr).getOperand() = v.getAnAccess()
      )
    )
  )
}

/**
 * Holds if function `f` contains a `put_device(arg)` whose argument is derived
 * from the acquire call `acq`.
 */
predicate hasMatchingPut(Function f, RefcountedDeviceAcquire acq) {
  exists(PutDeviceCall p |
    p.getEnclosingFunction() = f and
    derivedFrom(p.getArgument(0), acq, f)
  )
}

/**
 * Holds if there is an early-return path from `acq` that does NOT pass through
 * any `put_device(<derived>)` before the `return`.
 *
 * We approximate this with a simple CFG forward walk: starting at the acquire,
 * if we can reach a ReturnStmt without encountering a matching put_device on
 * that path, the query flags the acquire.
 */
predicate reachesReturnWithoutPut(RefcountedDeviceAcquire acq) {
  exists(Function f, ReturnStmt ret |
    acq.getEnclosingFunction() = f and
    ret.getEnclosingFunction() = f and
    // a CFG path exists from acq to ret
    acq.getASuccessor+() = ret and
    // and on at least one such path there is no put_device on the derived value
    not exists(PutDeviceCall p |
      p.getEnclosingFunction() = f and
      derivedFrom(p.getArgument(0), acq, f) and
      acq.getASuccessor+() = p and
      p.getASuccessor+() = ret
    )
  )
}

from RefcountedDeviceAcquire acq, Function f
where
  f = acq.getEnclosingFunction() and
  // require at least one matching put_device in the function (so we only flag
  // cases where the API is known to need releasing in this code base) ...
  hasMatchingPut(f, acq) and
  // ... but at least one path from this particular acquire to a return is
  // missing the put_device, indicating a leak on that path.
  reachesReturnWithoutPut(acq)
select acq,
  "Reference returned by $@ may leak: not all paths to return call put_device on the result.",
  acq.getTarget(), acq.getTarget().getName()
