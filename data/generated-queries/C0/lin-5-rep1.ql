/**
 * @name Missing put_device after of_find_device_by_node
 * @description of_find_device_by_node() and related lookup helpers take a reference on
 *              the returned struct device. Failing to call put_device() on every exit
 *              path (in particular error paths) results in a refcount leak.
 * @kind problem
 * @problem.severity warning
 * @id cpp/of-find-device-refcount-leak
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph

/**
 * Functions that return a `struct platform_device *` (or similar device pointer)
 * with an elevated reference count, requiring a matching `put_device()`.
 */
predicate isDeviceAcquiringCall(FunctionCall fc) {
  fc.getTarget().getName() in [
      "of_find_device_by_node",
      "bus_find_device",
      "bus_find_device_by_name",
      "bus_find_device_by_of_node",
      "driver_find_device",
      "driver_find_device_by_name",
      "driver_find_device_by_of_node",
      "class_find_device",
      "class_find_device_by_name",
      "class_find_device_by_of_node",
      "device_find_child",
      "device_find_child_by_name"
    ]
}

/** A call that releases a device reference. */
predicate isPutDeviceCall(FunctionCall fc, Expr arg) {
  fc.getTarget().getName() = "put_device" and
  arg = fc.getArgument(0)
}

/**
 * Holds if `e` is `&v->dev` or simply `v` referencing the local variable `v`
 * which holds the acquired device pointer.
 */
predicate refersToAcquiredDevice(Expr e, Variable v) {
  // pattern: put_device(&dev->dev) where dev is a struct platform_device *
  exists(AddressOfExpr ao, FieldAccess fa |
    e = ao and
    ao.getOperand() = fa and
    fa.getQualifier().(VariableAccess).getTarget() = v
  )
  or
  // pattern: put_device(dev) directly (when v already holds &something->dev)
  e.(VariableAccess).getTarget() = v
}

/** Holds if there is some put_device call in the function that releases v. */
predicate hasPutDeviceFor(Function f, Variable v) {
  exists(FunctionCall pc, Expr a |
    pc.getEnclosingFunction() = f and
    isPutDeviceCall(pc, a) and
    refersToAcquiredDevice(a, v)
  )
}

/**
 * A control-flow node within function `f` that is a return statement
 * reachable from the acquisition call without going through a put_device
 * release of `v`.
 */
predicate leakingReturn(Function f, Variable v, ReturnStmt rs, FunctionCall acq) {
  acq.getEnclosingFunction() = f and
  isDeviceAcquiringCall(acq) and
  acq.getParent*() instanceof Stmt and
  exists(AssignExpr ae |
    ae.getRValue() = acq and
    ae.getLValue().(VariableAccess).getTarget() = v
  )
  and
  rs.getEnclosingFunction() = f and
  // returning an error code (non-zero) — heuristic: returns a negative int constant
  // or a variable that holds an error. Keep simple: any ReturnStmt that is
  // CFG-reachable from acq.
  acq.getASuccessor+() = rs and
  // and there is NO put_device(v) on the path between acq and rs
  not exists(FunctionCall pc, Expr a |
    pc.getEnclosingFunction() = f and
    isPutDeviceCall(pc, a) and
    refersToAcquiredDevice(a, v) and
    acq.getASuccessor+() = pc and
    pc.getASuccessor+() = rs
  )
}

from Function f, Variable v, FunctionCall acq, ReturnStmt rs
where
  leakingReturn(f, v, rs, acq) and
  // suppress if the function never has any put_device for v — that's a different
  // (worse) bug, but also reported here as a leak.
  not hasPutDeviceFor(f, v) and
  // require that v is local to f
  v.(LocalVariable).getFunction() = f
select rs,
  "Possible refcount leak: '" + v.getName() + "' obtained via " +
    acq.getTarget().getName() + "() at $@ is not released by put_device() before this return.",
  acq, acq.getTarget().getName()
