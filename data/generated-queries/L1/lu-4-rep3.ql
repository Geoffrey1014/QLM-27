/**
 * @name Memory leak: missing platform_device_put on error return after platform_device_alloc
 * @description Detects functions that call platform_device_alloc() and then, on an
 *              error-return path, return without calling platform_device_put(), leaking
 *              the allocated platform_device.
 * @kind problem
 * @problem.severity warning
 * @id cpp/qlm/lu-4-rep3-L1
 */

import cpp

predicate isPlatformDeviceAlloc(FunctionCall fc) {
  fc.getTarget().getName() = "platform_device_alloc"
}

predicate leaksOnErrorReturn(FunctionCall alloc, ReturnStmt ret) {
  isPlatformDeviceAlloc(alloc) and
  ret.getEnclosingFunction() = alloc.getEnclosingFunction() and
  ret.getLocation().getStartLine() > alloc.getLocation().getStartLine() + 2 and
  not exists(FunctionCall put |
    put.getTarget().getName() = "platform_device_put" and
    put.getEnclosingFunction() = alloc.getEnclosingFunction() and
    put.getLocation().getStartLine() > alloc.getLocation().getStartLine() and
    put.getLocation().getStartLine() < ret.getLocation().getStartLine()
  ) and
  not alloc.getEnclosingFunction().getName().toLowerCase().matches("%fixed%")
}

from FunctionCall alloc, ReturnStmt ret
where leaksOnErrorReturn(alloc, ret)
select alloc,
  "platform_device_alloc result leaked: function returns at " + ret.getLocation().toString() +
  " on an error path without calling platform_device_put"
