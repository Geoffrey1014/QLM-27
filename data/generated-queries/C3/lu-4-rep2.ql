/**
 * @name Missing platform_device_put on error return after platform_device_alloc
 * @description Detects functions that call platform_device_alloc and then return
 *              on an error path without first calling platform_device_put,
 *              leaking the allocated platform_device.
 * @kind problem
 * @id cpp/qlllm/missing-platform-device-put
 * @problem.severity warning
 */

import cpp

predicate isAcquire(FunctionCall fc) {
  fc.getTarget().getName() = "platform_device_alloc"
}

predicate isRelease(FunctionCall fc) {
  fc.getTarget().getName() = "platform_device_put"
}

predicate leakyReturn(FunctionCall acquire, ReturnStmt ret) {
  isAcquire(acquire) and
  ret.getEnclosingFunction() = acquire.getEnclosingFunction() and
  exists(ControlFlowNode n | n = acquire.getASuccessor+() and n = ret) and
  not exists(FunctionCall rel |
    isRelease(rel) and
    rel.getEnclosingFunction() = acquire.getEnclosingFunction() and
    rel = acquire.getASuccessor+() and
    ret = rel.getASuccessor+()
  )
}

from FunctionCall acquire, ReturnStmt ret
where leakyReturn(acquire, ret)
select acquire,
  "platform_device_alloc result may leak: error-path return at $@ does not call platform_device_put first.",
  ret, "this return"
