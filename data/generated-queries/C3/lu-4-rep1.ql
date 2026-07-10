/**
 * @name Missing platform_device_put on error path after platform_device_alloc
 * @description Detects functions that allocate a platform_device via
 *              platform_device_alloc() but fail to release it via
 *              platform_device_put() on at least one error return path,
 *              causing a memory leak (CWE-401).
 * @kind problem
 * @problem.severity warning
 * @id cpp/qlm/c3/lu-4
 * @tags reliability
 *       correctness
 *       resource-leak
 */

import cpp

predicate isPlatformDeviceAlloc(FunctionCall fc) {
  fc.getTarget().getName() = "platform_device_alloc"
}

Variable acquiredVariable(FunctionCall fc) {
  isPlatformDeviceAlloc(fc) and
  exists(VariableAccess va |
    va = fc.getParent().(AssignExpr).getLValue() and
    result = va.getTarget()
  )
}

predicate hasReleaseOnAllErrorPaths(FunctionCall acquire) {
  isPlatformDeviceAlloc(acquire) and
  forall(ReturnStmt rs |
    rs.getEnclosingFunction() = acquire.getEnclosingFunction() and
    rs.getLocation().getStartLine() > acquire.getLocation().getStartLine()
  |
    exists(FunctionCall release |
      release.getTarget().getName() = "platform_device_put" and
      release.getEnclosingFunction() = acquire.getEnclosingFunction() and
      release.getLocation().getStartLine() < rs.getLocation().getStartLine() and
      release.getLocation().getStartLine() > acquire.getLocation().getStartLine()
    )
  )
}

from FunctionCall acquire
where
  isPlatformDeviceAlloc(acquire) and
  exists(ReturnStmt rs |
    rs.getEnclosingFunction() = acquire.getEnclosingFunction() and
    rs.getLocation().getStartLine() > acquire.getLocation().getStartLine() and
    not exists(FunctionCall release |
      release.getTarget().getName() = "platform_device_put" and
      release.getEnclosingFunction() = acquire.getEnclosingFunction() and
      release.getLocation().getStartLine() > acquire.getLocation().getStartLine() and
      release.getLocation().getStartLine() < rs.getLocation().getStartLine()
    )
  )
select acquire,
  "Potential platform_device leak: missing platform_device_put on error return path after platform_device_alloc"
