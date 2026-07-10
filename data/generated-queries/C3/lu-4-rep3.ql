/**
 * @name C3 generated query for lu-4 / fix 9bbfceea12a8
 * @description Missing platform_device_put after platform_device_alloc on error return path — memory leak (CWE-401)
 * @kind problem
 * @problem.severity warning
 * @id cpp/rq3/c3/lu-4-rep3
 */

import cpp

predicate isPlatformDeviceAlloc(FunctionCall fc) {
  fc.getTarget().getName() = "platform_device_alloc"
}

predicate isPlatformDevicePut(FunctionCall fc) {
  fc.getTarget().getName() = "platform_device_put"
}

predicate errorCheckReturn(IfStmt ifs, ReturnStmt ret) {
  ret.getParent*() = ifs.getThen() and
  exists(FunctionCall callInCond |
    ifs.getCondition().getAChild*() = callInCond
    or
    exists(VariableAccess va |
      ifs.getCondition().getAChild*() = va and
      exists(AssignExpr ae |
        ae.getLValue() = va.getTarget().getAnAccess() and
        ae.getRValue() = callInCond and
        callInCond.getEnclosingFunction() = ifs.getEnclosingFunction()
      )
    )
  )
}

predicate leakingErrorReturn(FunctionCall alloc, ReturnStmt ret) {
  isPlatformDeviceAlloc(alloc) and
  ret.getEnclosingFunction() = alloc.getEnclosingFunction() and
  ret.getLocation().getStartLine() > alloc.getLocation().getStartLine() + 2 and
  exists(IfStmt ifs | errorCheckReturn(ifs, ret) and
    ifs.getEnclosingFunction() = alloc.getEnclosingFunction()) and
  not exists(FunctionCall put |
    isPlatformDevicePut(put) and
    put.getEnclosingFunction() = alloc.getEnclosingFunction() and
    put.getLocation().getStartLine() > alloc.getLocation().getStartLine() and
    put.getLocation().getStartLine() < ret.getLocation().getStartLine()
  )
}

predicate isInFixedFunction(FunctionCall fc) {
  fc.getEnclosingFunction().getName().toLowerCase().matches("%fixed%")
}

from FunctionCall alloc, ReturnStmt ret
where
  isPlatformDeviceAlloc(alloc) and
  not isInFixedFunction(alloc) and
  leakingErrorReturn(alloc, ret)
select alloc,
  "platform_device_alloc result leaked: function returns at " + ret.getLocation().toString() +
  " on an error path without calling platform_device_put"
