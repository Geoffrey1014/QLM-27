/**
 * @name Missing put_device after of_find_device_by_node
 * @description of_find_device_by_node() returns a struct platform_device*
 *              with the underlying struct device refcount incremented.
 *              The caller must release the reference via
 *              put_device(&pdev->dev) on every exit path. Failing to do
 *              so leaks the device refcount (CWE-401).
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-lin-5
 */

import cpp

/**
 * APIs returning a struct platform_device* (or related driver-bound
 * struct device wrapper) whose underlying device refcount has been
 * incremented and must be released by the caller via put_device().
 */
predicate isPlatformDeviceAcquireApi(string name) {
  name = "of_find_device_by_node" or
  name = "bus_find_device" or
  name = "bus_find_device_by_name" or
  name = "driver_find_device" or
  name = "class_find_device"
}

/** A call to put_device(). */
predicate isPutDeviceCall(FunctionCall c) {
  c.getTarget().getName() = "put_device"
}

/**
 * The Variable receiving the return value of `call`, either via
 * initialization (`T *v = call(...)`) or by assignment
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
 * True iff some put_device() call inside `f` is passed an argument that
 * reads the `dev` field of `v` (i.e. &v->dev) -- the canonical release
 * pattern for refcounted struct device wrappers.
 */
predicate releasesDeviceField(Function f, Variable v) {
  exists(FunctionCall put, AddressOfExpr addr, FieldAccess fa |
    isPutDeviceCall(put) and
    put.getEnclosingFunction() = f and
    addr = put.getArgument(0) and
    fa = addr.getOperand() and
    fa.getQualifier().(VariableAccess).getTarget() = v and
    fa.getTarget().getName() = "dev"
  )
  or
  // Fallback: put_device called directly with v (already a struct device*).
  exists(FunctionCall put, VariableAccess va |
    isPutDeviceCall(put) and
    put.getEnclosingFunction() = f and
    va = put.getArgument(0) and
    va.getTarget() = v
  )
}

from FunctionCall acquire, Variable recv, Function enclosing
where
  isPlatformDeviceAcquireApi(acquire.getTarget().getName()) and
  recv = receiverVariableOf(acquire) and
  enclosing = acquire.getEnclosingFunction() and
  not releasesDeviceField(enclosing, recv)
select acquire,
  "Call to " + acquire.getTarget().getName() +
    " stores a refcounted device in '" + recv.getName() +
    "' but the enclosing function never calls put_device() on it -- reference leak."
