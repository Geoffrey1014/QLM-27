/**
 * @name Refcount leak: missing put_device after of_find_device_by_node
 * @description Detects functions that call of_find_device_by_node() and
 *              take a reference on a struct platform_device but never
 *              release it via put_device().
 * @kind problem
 * @problem.severity warning
 * @id qlm/lin-5-rep1-l1
 */

import cpp

predicate isAcquireCall(FunctionCall fc) {
  fc.getTarget().getName() = "of_find_device_by_node"
}

predicate hasPutDeviceRelease(Function f) {
  exists(FunctionCall rel |
    rel.getEnclosingFunction() = f and
    rel.getTarget().getName() = "put_device"
  )
}

from FunctionCall acquire, Function enclosing
where
  isAcquireCall(acquire) and
  enclosing = acquire.getEnclosingFunction() and
  not hasPutDeviceRelease(enclosing)
select acquire,
  "Missing put_device() after of_find_device_by_node() -- refcount leak in " + enclosing.getName()
