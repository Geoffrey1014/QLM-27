/**
 * @name Platform device leak: missing platform_device_put on return path
 * @description After a successful platform_device_alloc, returning from the
 *              function without a platform_device_put leaks the device.
 * @kind problem
 * @problem.severity warning
 * @id cpp/platform-device-put-leak
 */

import cpp

predicate isPlatformDeviceAlloc(FunctionCall fc) { fc.getTarget().getName() = "platform_device_alloc" }

predicate isPlatformDevicePut(FunctionCall fc) { fc.getTarget().getName() = "platform_device_put" }

predicate hasLeakingReturn(FunctionCall acquire, ReturnStmt rs) {
  isPlatformDeviceAlloc(acquire) and
  rs.getEnclosingFunction() = acquire.getEnclosingFunction() and
  rs.getLocation().getStartLine() > acquire.getLocation().getStartLine() and
  not exists(FunctionCall release |
    isPlatformDevicePut(release) and
    release.getEnclosingFunction() = acquire.getEnclosingFunction() and
    release.getLocation().getStartLine() > acquire.getLocation().getStartLine() and
    release.getLocation().getStartLine() < rs.getLocation().getStartLine())
}

from FunctionCall acquire, ReturnStmt rs
where hasLeakingReturn(acquire, rs)
select acquire,
  "Potential platform_device leak: missing platform_device_put on return path at line $@",
  rs, rs.toString()
