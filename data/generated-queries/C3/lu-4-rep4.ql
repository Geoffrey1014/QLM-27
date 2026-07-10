/**
 * @name C3 generated query for lu-4 / fix 9bbfceea12a8
 * @description Missing platform_device_put on error return path after platform_device_alloc — memory leak (CWE-401)
 * @kind problem
 * @problem.severity warning
 * @id cpp/rq3/c3/lu-4-rep4
 */

import cpp

predicate isPlatformDeviceAlloc(FunctionCall fc) {
  fc.getTarget().getName() = "platform_device_alloc"
}

predicate isPlatformDevicePut(FunctionCall fc) {
  fc.getTarget().getName() = "platform_device_put"
}

Variable getAcquiredVariable(FunctionCall acquire) {
  exists(AssignExpr assign |
    assign.getRValue() = acquire and
    result = assign.getLValue().(VariableAccess).getTarget()
  )
  or
  exists(FieldAccess fa, AssignExpr assign |
    assign.getRValue() = acquire and
    assign.getLValue() = fa and
    result = fa.getTarget()
  )
}

/* A buggy acquire: there exists a non-zero ReturnStmt textually after
 * the acquire with no platform_device_put call appearing between the
 * acquire and the return (line-number scan, intraprocedural). */
predicate hasReturnAfterAcquireWithoutPut(FunctionCall acquire) {
  isPlatformDeviceAlloc(acquire) and
  exists(ReturnStmt rs |
    rs.getEnclosingFunction() = acquire.getEnclosingFunction() and
    rs.getLocation().getStartLine() > acquire.getLocation().getStartLine() and
    /* skip the success return (return 0) — only error returns leak */
    not rs.getExpr().(Literal).getValue() = "0" and
    not exists(FunctionCall put |
      isPlatformDevicePut(put) and
      put.getEnclosingFunction() = acquire.getEnclosingFunction() and
      put.getLocation().getStartLine() > acquire.getLocation().getStartLine() and
      put.getLocation().getStartLine() <= rs.getLocation().getStartLine()
    )
  )
}

from FunctionCall acquire
where
  isPlatformDeviceAlloc(acquire) and
  hasReturnAfterAcquireWithoutPut(acquire) and
  not acquire.getEnclosingFunction().getName().toLowerCase().matches("%fixed%") and
  not acquire.getEnclosingFunction().getName().toLowerCase().matches("%_fp_%")
select acquire,
  "Potential platform_device memory leak: missing platform_device_put on an error return path after platform_device_alloc in '" +
    acquire.getEnclosingFunction().getName() + "'"
