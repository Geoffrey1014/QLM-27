/**
 * @name pm_runtime_get_sync missing pm_runtime_put on error path
 * @description Detects pm_runtime_get_sync callers that fail to release
 *              the runtime PM refcount on the error return path.
 *              Pattern from commit f141a422159a (Lu-style four-features).
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3-l1-lu3-rep1
 */

import cpp

predicate isPmRuntimeGetSync(FunctionCall fc) {
  fc.getTarget().getName() = "pm_runtime_get_sync"
}

predicate hasMatchingPutInSameFunction(FunctionCall getCall) {
  exists(FunctionCall putCall |
    putCall.getEnclosingFunction() = getCall.getEnclosingFunction()
    and putCall.getTarget().getName() = "pm_runtime_put"
  )
}

from FunctionCall getCall, IfStmt errCheck, ReturnStmt errRet
where isPmRuntimeGetSync(getCall)
  and errCheck.getEnclosingFunction() = getCall.getEnclosingFunction()
  and errRet.getEnclosingFunction() = getCall.getEnclosingFunction()
  and errCheck.getLocation().getStartLine() > getCall.getLocation().getStartLine()
  and errRet.getLocation().getStartLine() > errCheck.getLocation().getStartLine()
  and errRet.getLocation().getStartLine() - errCheck.getLocation().getStartLine() <= 2
  and not exists(FunctionCall putCall |
         putCall.getEnclosingFunction() = getCall.getEnclosingFunction()
         and putCall.getTarget().getName() = "pm_runtime_put"
         and putCall.getLocation().getStartLine() > errCheck.getLocation().getStartLine()
         and putCall.getLocation().getStartLine() < errRet.getLocation().getStartLine())
select getCall,
  "pm_runtime_get_sync error-path missing pm_runtime_put in " +
  getCall.getEnclosingFunction().getName()
