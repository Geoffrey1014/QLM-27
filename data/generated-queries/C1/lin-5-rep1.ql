/**
 * @name Missing put_device after of_find_device_by_node
 * @description of_find_device_by_node() returns a struct platform_device*
 *              whose underlying struct device refcount has been
 *              incremented. The caller is responsible for releasing the
 *              reference via put_device(&dev->dev). If the enclosing
 *              function never invokes put_device() on the receiver
 *              variable's embedded `dev` member, the platform_device
 *              reference leaks (CWE-401).
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-lin-5
 */

import cpp

/**
 * Linux APIs that return a struct platform_device* / struct device*
 * with the underlying device refcount incremented. The caller must
 * balance with put_device().
 */
predicate isDeviceAcquireApi(string name) {
  name = "of_find_device_by_node" or
  name = "bus_find_device" or
  name = "bus_find_device_by_name" or
  name = "class_find_device" or
  name = "driver_find_device" or
  name = "get_device"
}

/** True if `c` is a call to put_device(). */
predicate isPutDevice(FunctionCall c) {
  c.getTarget().getName() = "put_device"
}

/**
 * The Variable that captures the return value of `call`, either via
 * initialization (`T *v = call(...)`) or via assignment
 * (`v = call(...)`).
 */
Variable receiverVariableOf(FunctionCall call) {
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
 * True iff some put_device() inside `f` is passed an expression that
 * mentions a read of `v`. This intentionally includes both bare
 * `put_device(v)` (when v is itself a `struct device *`) and
 * `put_device(&v->dev)` (when v is a `struct platform_device *` and
 * the address-of expression accesses its `dev` field).
 */
predicate releasesVariable(Function f, Variable v) {
  exists(FunctionCall put, VariableAccess arg |
    isPutDevice(put) and
    put.getEnclosingFunction() = f and
    arg = put.getArgument(0).getAChild*() and
    arg.getTarget() = v
  )
  or
  exists(FunctionCall put, VariableAccess arg |
    isPutDevice(put) and
    put.getEnclosingFunction() = f and
    arg = put.getArgument(0) and
    arg.getTarget() = v
  )
}

from FunctionCall acquire, Variable recv, Function enclosing
where
  isDeviceAcquireApi(acquire.getTarget().getName()) and
  recv = receiverVariableOf(acquire) and
  enclosing = acquire.getEnclosingFunction() and
  not releasesVariable(enclosing, recv)
select acquire,
  "Call to " + acquire.getTarget().getName() +
    " stores a refcounted device in '" + recv.getName() +
    "' but the enclosing function never calls put_device() on it -- reference leak."
