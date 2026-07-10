/**
 * @name Refcount leak of of_find_device_by_node
 * @description of_find_device_by_node takes a reference on the returned
 *              platform_device. If put_device(&dev->dev) is not called on
 *              every exit path, the refcount leaks.
 * @kind problem
 * @problem.severity warning
 * @id cpp/kernel/of-find-device-by-node-refcount-leak
 * @tags security correctness reliability
 */

import cpp

/**
 * A call to `of_find_device_by_node`, which takes a reference on the
 * returned `struct platform_device *` that the caller must release via
 * `put_device(&dev->dev)`.
 */
predicate isOfFindDeviceByNodeCall(FunctionCall fc) {
  fc.getTarget().getName() = "of_find_device_by_node"
}

/**
 * `put_device` call inside `f`.
 */
predicate hasPutDeviceCall(Function f) {
  exists(FunctionCall release |
    release.getTarget().getName() = "put_device" and
    release.getEnclosingFunction() = f
  )
}

from FunctionCall acquire, Function enclosing
where
  isOfFindDeviceByNodeCall(acquire) and
  enclosing = acquire.getEnclosingFunction() and
  not hasPutDeviceCall(enclosing)
select acquire,
  "Possible refcount leak: of_find_device_by_node called in $@ but no put_device release found in the same function.",
  enclosing, enclosing.getName()
