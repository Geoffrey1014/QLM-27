/**
 * @name Missing put_device after of_find_device_by_node
 * @description of_find_device_by_node() (and related helpers) returns a
 *              struct platform_device* whose embedded struct device has
 *              had its refcount incremented. The caller must release the
 *              reference via put_device(&pdev->dev) on every successful
 *              path; otherwise the device leaks (CWE-401).
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-lin-5
 */

import cpp

/* Acquire APIs: device-tree / driver-model lookups that return a
 * platform_device* (or device*) with the refcount bumped. */
predicate isDeviceAcquireApi(string name) {
  name = "of_find_device_by_node" or
  name = "bus_find_device_by_name" or
  name = "bus_find_device_by_of_node" or
  name = "bus_find_device" or
  name = "driver_find_device" or
  name = "class_find_device" or
  name = "class_find_device_by_name" or
  name = "class_find_device_by_of_node" or
  name = "device_find_child" or
  name = "get_device"
}

/* Calls that release the reference. put_device() is the canonical
 * release; some wrappers exist (e.g. platform_device_put). */
predicate isDeviceReleaseCall(FunctionCall c) {
  c.getTarget().getName() = "put_device" or
  c.getTarget().getName() = "platform_device_put" or
  c.getTarget().getName() = "of_dev_put"
}

/* The Variable that receives `call`'s return value, either via
 * initialization (`T *v = call(...)`) or assignment (`v = call(...)`). */
Variable getReceiverVariable(FunctionCall call) {
  exists(Variable v |
    v.getInitializer().getExpr() = call and result = v
  )
  or
  exists(AssignExpr a |
    a.getRValue() = call and
    result = a.getLValue().(VariableAccess).getTarget()
  )
}

/* True if `f` contains a release call whose argument transitively reads
 * the variable `v`. We allow the common idiom `put_device(&v->dev)` by
 * looking for any VariableAccess of `v` nested inside the release call's
 * argument subtree. */
predicate hasReleaseInFunction(Function f, Variable v) {
  exists(FunctionCall put, VariableAccess va |
    isDeviceReleaseCall(put) and
    put.getEnclosingFunction() = f and
    va = put.getAnArgument().getAChild*() and
    va.getTarget() = v
  )
  or
  exists(FunctionCall put, VariableAccess va |
    isDeviceReleaseCall(put) and
    put.getEnclosingFunction() = f and
    va = put.getAnArgument() and
    va.getTarget() = v
  )
}

from FunctionCall acquire, Variable v, Function f
where
  isDeviceAcquireApi(acquire.getTarget().getName()) and
  v = getReceiverVariable(acquire) and
  f = acquire.getEnclosingFunction() and
  not hasReleaseInFunction(f, v)
select acquire,
  "Call to " + acquire.getTarget().getName() +
    " stores a refcounted device in '" + v.getName() +
    "' but the enclosing function never calls put_device() on it -- reference leak."
