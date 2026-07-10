/**
 * @name Refcount leak: missing put_device after of_find_device_by_node
 * @description Detects functions that call of_find_device_by_node() and
 *              take a reference on a struct platform_device but never
 *              release it via put_device(&dev->dev).
 * @kind problem
 * @problem.severity warning
 * @id qlm/lin-5-rep1-l0
 */

import cpp

predicate isAcquireCall(FunctionCall fc) {
  fc.getTarget().getName() = "of_find_device_by_node"
}

from FunctionCall acquire, Function enclosing
where
  isAcquireCall(acquire) and
  enclosing = acquire.getEnclosingFunction() and
  not exists(FunctionCall rel |
    rel.getEnclosingFunction() = enclosing and
    rel.getTarget().getName() = "put_device"
  )
select acquire,
  "Missing put_device() after of_find_device_by_node() -- refcount leak."
