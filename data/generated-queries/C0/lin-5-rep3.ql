/**
 * @name Missing put_device after of_find_device_by_node
 * @description of_find_device_by_node() takes a reference to the underlying
 *              struct device. The caller must release it with put_device() on
 *              every path that exits the enclosing function after the call,
 *              otherwise the device reference count leaks.
 * @kind problem
 * @problem.severity warning
 * @id cpp/of-find-device-by-node-refleak
 * @tags correctness
 *       reliability
 *       resource-leak
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph
import semmle.code.cpp.controlflow.Guards

/**
 * Acquiring calls of the of_find_*_by_node() family that return a refcounted
 * pointer the caller is responsible for releasing.
 *
 * Each entry pairs the acquire-API name with the cleanup-API name that
 * releases the reference it returned.
 */
predicate acquireReleasePair(string acquire, string release) {
  acquire = "of_find_device_by_node" and release = "put_device"
  or
  acquire = "of_find_i2c_device_by_node" and release = "put_device"
  or
  acquire = "of_find_spi_device_by_node" and release = "put_device"
  or
  acquire = "of_find_mii_bus_by_node" and release = "put_device"
  or
  acquire = "of_find_backlight_by_node" and release = "put_device"
  or
  acquire = "of_find_net_device_by_node" and release = "dev_put"
}

/** A call to one of the acquire APIs. */
class AcquireCall extends FunctionCall {
  string releaseName;

  AcquireCall() {
    exists(string acquire |
      acquireReleasePair(acquire, releaseName) and
      this.getTarget().getName() = acquire
    )
  }

  string getReleaseName() { result = releaseName }
}

/**
 * Holds if `fc` is a call to the release function paired with `acq`, taking
 * an argument that could plausibly refer to the resource produced by `acq`.
 *
 * For of_find_device_by_node()-style APIs the release is typically called as
 * put_device(&dev->dev), so we accept any call whose argument transitively
 * mentions a variable that aliases the value returned by `acq`.
 */
predicate isPairedRelease(AcquireCall acq, FunctionCall fc) {
  fc.getTarget().getName() = acq.getReleaseName() and
  (
    // Direct: put_device(dev) where dev = acq
    exists(Variable v |
      acq.getEnclosingFunction() = fc.getEnclosingFunction() and
      assignsFrom(v, acq) and
      fc.getAnArgument().(VariableAccess).getTarget() = v
    )
    or
    // Field access: put_device(&dev->dev) where dev = acq
    exists(Variable v, VariableAccess va |
      acq.getEnclosingFunction() = fc.getEnclosingFunction() and
      assignsFrom(v, acq) and
      va.getTarget() = v and
      fc.getAnArgument().getAChild*() = va
    )
  )
}

/** Holds if variable `v` is assigned from the result of acquire call `acq`. */
predicate assignsFrom(Variable v, AcquireCall acq) {
  v.getAnAssignedValue() = acq
  or
  exists(AssignExpr ae | ae.getLValue().(VariableAccess).getTarget() = v and ae.getRValue() = acq)
}

/**
 * Holds if there exists a control-flow path from `acq` to `exit` that does
 * NOT pass through a paired release call.
 */
predicate leakingPath(AcquireCall acq, ReturnStmt exit) {
  exit.getEnclosingFunction() = acq.getEnclosingFunction() and
  reachableWithoutRelease(acq, exit, acq)
}

/**
 * Forward CFG reachability from `start` to `sink`, where `start` is a successor
 * of (or equal to) the acquire call, and no node on the path is a paired
 * release for `acq`.
 */
predicate reachableWithoutRelease(ControlFlowNode start, ControlFlowNode sink, AcquireCall acq) {
  start = acq.getASuccessor() and
  start = sink
  or
  exists(ControlFlowNode mid |
    reachableWithoutRelease(start, mid, acq) and
    not isPairedRelease(acq, mid) and
    sink = mid.getASuccessor()
  )
  or
  // Bootstrap: from acq itself
  start = acq and sink = acq.getASuccessor()
}

from AcquireCall acq, ReturnStmt ret
where
  leakingPath(acq, ret) and
  // Suppress cases where the function returns the acquired pointer itself
  // (ownership transferred to caller).
  not exists(Variable v |
    assignsFrom(v, acq) and
    ret.getExpr().(VariableAccess).getTarget() = v
  ) and
  not ret.getExpr() = acq
select acq,
  "Reference acquired by " + acq.getTarget().getName() +
    "() may leak: this return statement is reachable without a matching " +
    acq.getReleaseName() + "() call. Return at $@.", ret, ret.getLocation().toString()
