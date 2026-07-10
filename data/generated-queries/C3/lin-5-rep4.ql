/**
 * @name C3 generated query for lin-5 / fix 10d6bdf53290
 * @description Missing put_device(&pdev->dev) after of_find_device_by_node — platform_device refcount leak (CWE-911)
 * @kind problem
 * @problem.severity warning
 * @id cpp/rq3/c3/lin-5-rep4
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
    isRelease(rel) and
    rel.getEnclosingFunction() = acq.getEnclosingFunction())
}

from FunctionCall acq, Function f
where
  isAcquire(acq) and
  f = acq.getEnclosingFunction() and
  hasMissingRelease(acq) and
  not f.getName().matches("%_fixed%")
select acq,
  "platform_device refcount leak: of_find_device_by_node return value not released via put_device() in function " +
    f.getName()
