/**
 * @name Missing put_device after platform-device lookup by node
 * @description A Linux helper such as of_find_device_by_node() returns
 *              a struct platform_device* whose embedded struct device
 *              has had its refcount incremented. If the enclosing
 *              function never releases the reference via put_device()
 *              on `&<dev>->dev`, the platform_device reference leaks
 *              (CWE-401).
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-lin-5
 */

import cpp

/**
 * Linux APIs that return a struct platform_device* (or compatible bus
 * device wrapper) whose underlying struct device refcount has been
 * incremented. The caller owns the reference and must release it via
 * put_device(&dev->dev).
 */
predicate isRefcountedDeviceLookup(string name) {
  name = "of_find_device_by_node" or
  name = "bus_find_device" or
  name = "bus_find_device_by_name" or
  name = "bus_find_device_by_of_node" or
  name = "driver_find_device" or
  name = "class_find_device" or
  name = "class_find_device_by_name" or
  name = "class_find_device_by_of_node"
}

/** True if `c` is a call to put_device(). */
predicate isPutDeviceCall(FunctionCall c) {
  c.getTarget().getName() = "put_device"
}

/**
 * The variable that captures the return value of `call`, either by
 * declaration-initializer or by a top-level assignment.
 */
Variable resultSink(FunctionCall call) {
  exists(Variable v |
    v.getInitializer().getExpr() = call and
    result = v
  )
  or
  exists(AssignExpr a, VariableAccess lhs |
    a.getRValue() = call and
    lhs = a.getLValue() and
    result = lhs.getTarget()
  )
}

/**
 * True iff some put_device() call inside function `f` takes
 * `&<receiver>->dev` (or `&<receiver>.dev`) as its first argument,
 * i.e. it releases the same platform_device captured in `receiver`.
 */
predicate hasMatchingPutDevice(Function f, Variable receiver) {
  exists(FunctionCall put, Expr arg, FieldAccess fa, AddressOfExpr addr |
    isPutDeviceCall(put) and
    put.getEnclosingFunction() = f and
    arg = put.getArgument(0) and
    addr = arg and
    fa = addr.getOperand() and
    fa.getQualifier().(VariableAccess).getTarget() = receiver and
    fa.getTarget().getName() = "dev"
  )
}

/**
 * Fallback: handle the case where the caller passes the receiver
 * directly (e.g. `put_device(devVar)`), which is rarer but valid for
 * APIs that already return a `struct device *`.
 */
predicate hasDirectPutDevice(Function f, Variable receiver) {
  exists(FunctionCall put, VariableAccess va |
    isPutDeviceCall(put) and
    put.getEnclosingFunction() = f and
    va = put.getArgument(0) and
    va.getTarget() = receiver
  )
}

from FunctionCall acquire, Variable recv, Function enclosing
where
  isRefcountedDeviceLookup(acquire.getTarget().getName()) and
  recv = resultSink(acquire) and
  enclosing = acquire.getEnclosingFunction() and
  not hasMatchingPutDevice(enclosing, recv) and
  not hasDirectPutDevice(enclosing, recv)
select acquire,
  "Call to " + acquire.getTarget().getName() +
    " stores a refcounted device in '" + recv.getName() +
    "' but the enclosing function never releases it via put_device() -- reference leak."
