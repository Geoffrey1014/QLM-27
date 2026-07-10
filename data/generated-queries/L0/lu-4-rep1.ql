/**
 * @name Missing platform_device_put on error path after platform_device_alloc
 * @description Detects functions that allocate a platform_device via
 *              platform_device_alloc() but fail to release it via
 *              platform_device_put() on at least one error return path,
 *              causing a memory leak (CWE-401).
 * @kind problem
 * @problem.severity warning
 * @id qlm/l0-lu4-platform-device-leak
 * @tags reliability
 *       correctness
 *       resource-leak
 */

import cpp

predicate isPlatformDeviceAlloc(FunctionCall fc) {
  fc.getTarget().getName() = "platform_device_alloc"
}

from FunctionCall acquire, Function enclosing
where
  isPlatformDeviceAlloc(acquire) and
  enclosing = acquire.getEnclosingFunction() and
  exists(ReturnStmt rs |
    rs.getEnclosingFunction() = enclosing and
    rs.getLocation().getStartLine() > acquire.getLocation().getStartLine() and
    not exists(FunctionCall release |
      release.getTarget().getName() = "platform_device_put" and
      release.getEnclosingFunction() = enclosing and
      release.getLocation().getStartLine() > acquire.getLocation().getStartLine() and
      release.getLocation().getStartLine() < rs.getLocation().getStartLine()
    )
  ) and
  not enclosing.getName().toLowerCase().matches("%fixed%")
select acquire,
  "Potential platform_device leak: missing platform_device_put on error return path after platform_device_alloc in '"
    + enclosing.getName() + "'"
