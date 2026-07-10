/**
 * @name Missing platform_device_put on error path after platform_device_alloc
 * @description Detects functions that call platform_device_alloc() but return
 *              on an error path without calling platform_device_put(), leaking
 *              the allocated platform device. Pattern from commit 9bbfceea12a8.
 * @kind problem
 * @problem.severity warning
 * @id cpp/missing-platform-device-put
 */

import cpp

predicate isPlatformDeviceAllocCall(FunctionCall fc) {
  fc.getTarget().getName() = "platform_device_alloc"
}

predicate returnStmtInFunctionAfterAcquire(ReturnStmt r, FunctionCall acq) {
  isPlatformDeviceAllocCall(acq) and
  r.getEnclosingFunction() = acq.getEnclosingFunction() and
  not exists(FunctionCall put |
    put.getTarget().getName() = "platform_device_put" and
    put.getEnclosingFunction() = r.getEnclosingFunction()
  )
}

from Function f, FunctionCall acq, ReturnStmt r
where
  isPlatformDeviceAllocCall(acq) and
  acq.getEnclosingFunction() = f and
  r.getEnclosingFunction() = f and
  r.getLocation().getStartLine() > acq.getLocation().getStartLine() and
  not exists(Expr e | e = r.getExpr() and e.getValue() = "0") and
  not exists(FunctionCall put |
    put.getTarget().getName() = "platform_device_put" and
    put.getEnclosingFunction() = f and
    put.getLocation().getStartLine() < r.getLocation().getStartLine()
  ) and
  not exists(GotoStmt g |
    g.getEnclosingFunction() = f and
    g.getLocation().getStartLine() = r.getLocation().getStartLine() - 1
  )
select r,
  "potential missing platform_device_put on error return after platform_device_alloc in $@",
  f, f.getName()
