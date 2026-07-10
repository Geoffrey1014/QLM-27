/**
 * @name platform_device refcount leak (of_find_device_by_node without put_device)
 * @description Detects functions that call of_find_device_by_node without any
 *              put_device() in the same function, indicating a likely refcount leak.
 * @kind problem
 * @problem.severity warning
 * @id cpp/lin-5-rep5/of-find-device-by-node-leak
 */

import cpp

predicate isAcquire(FunctionCall fc) {
  fc.getTarget().getName() = "of_find_device_by_node"
}

predicate isRelease(FunctionCall fc) {
  fc.getTarget().getName() = "put_device"
}

predicate hasMissingRelease(FunctionCall acq) {
  isAcquire(acq) and
  not exists(FunctionCall rel |
    isRelease(rel) and rel.getEnclosingFunction() = acq.getEnclosingFunction()
  )
}

from FunctionCall acq, Function f
where
  isAcquire(acq) and
  hasMissingRelease(acq) and
  f = acq.getEnclosingFunction()
select acq, "Possible refcount leak: of_find_device_by_node() called in $@ without put_device().",
  f, f.getName()
