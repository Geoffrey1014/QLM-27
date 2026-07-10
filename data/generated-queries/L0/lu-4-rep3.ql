/**
 * @name L0 generated query for lu-4 / fix 9bbfceea12a8
 * @description Missing platform_device_put after platform_device_alloc on error return path — memory leak (CWE-401)
 * @kind problem
 * @problem.severity warning
 * @id cpp/rq3/l0/lu-4-rep3
 */

import cpp

predicate leaksPlatformDevice(FunctionCall acquire, ReturnStmt leakingRet) {
  acquire.getTarget().getName() = "platform_device_alloc" and
  leakingRet.getEnclosingFunction() = acquire.getEnclosingFunction() and
  leakingRet.getLocation().getStartLine() > acquire.getLocation().getStartLine() and
  not exists(FunctionCall put |
    put.getTarget().getName() = "platform_device_put" and
    put.getEnclosingFunction() = acquire.getEnclosingFunction() and
    put.getLocation().getStartLine() > acquire.getLocation().getStartLine() and
    put.getLocation().getStartLine() < leakingRet.getLocation().getStartLine()
  ) and
  not exists(GotoStmt g |
    g.getEnclosingFunction() = acquire.getEnclosingFunction() and
    g.getLocation().getStartLine() > acquire.getLocation().getStartLine() and
    g.getLocation().getStartLine() < leakingRet.getLocation().getStartLine() and
    g.getTarget().getLocation().getStartLine() > leakingRet.getLocation().getStartLine()
  ) and
  not acquire.getEnclosingFunction().getName().toLowerCase().matches("%fixed%")
}

from FunctionCall acquire, ReturnStmt leakingRet
where leaksPlatformDevice(acquire, leakingRet)
select acquire,
  "Missing platform_device_put on error return at " + leakingRet.getLocation().toString() +
  " after platform_device_alloc in '" + acquire.getEnclosingFunction().getName() + "' — memory leak (CWE-401)"
