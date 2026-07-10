/**
 * @name Missing put_device after of_find_device_by_node
 * @description of_find_device_by_node() takes a reference on the returned
 *              platform_device. Callers must release it via put_device() on
 *              all exit paths, otherwise the refcount leaks.
 * @kind problem
 * @problem.severity warning
 * @id cpp/qlllm/rq3-d5-l1/lin-5-rep5
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
where isAcquireCall(acquire)
  and enclosing = acquire.getEnclosingFunction()
  and not hasPutDeviceRelease(enclosing)
select acquire,
  "Missing put_device() after of_find_device_by_node() -- refcount leak in " + enclosing.getName()
