/**
 * @name Missing platform_device_put on error path after platform_device_alloc
 * @description Detects functions where platform_device_alloc succeeds and a
 *              later error return skips the err: label that releases the
 *              allocated platform_device via platform_device_put, causing a
 *              memory leak.
 * @kind problem
 * @problem.severity warning
 * @id qlm/lu-4-rep5
 */

import cpp

predicate isMissingPutOnErrorPath(FunctionCall acquireCall, ReturnStmt leakyReturn) {
  acquireCall.getTarget().getName() = "platform_device_alloc" and
  exists(Function fn |
    acquireCall.getEnclosingFunction() = fn and
    leakyReturn.getEnclosingFunction() = fn and
    // return happens after the acquire (structurally later in the function)
    acquireCall.getLocation().getStartLine() < leakyReturn.getLocation().getStartLine() and
    // no platform_device_put call between the acquire and the return in the same function
    not exists(FunctionCall releaseCall |
      releaseCall.getTarget().getName() = "platform_device_put" and
      releaseCall.getEnclosingFunction() = fn and
      releaseCall.getLocation().getStartLine() > acquireCall.getLocation().getStartLine() and
      releaseCall.getLocation().getStartLine() < leakyReturn.getLocation().getStartLine()
    ) and
    // the return is guarded by an error condition (rules out the trivial 'return 0' happy path)
    exists(IfStmt guard |
      guard.getEnclosingFunction() = fn and
      guard.getThen().getAChild*() = leakyReturn and
      guard.getLocation().getStartLine() > acquireCall.getLocation().getStartLine()
    ) and
    // there IS an error-cleanup label later that does call platform_device_put
    // (i.e. the function has a working err: path, but THIS return skips it)
    exists(FunctionCall labeledRelease |
      labeledRelease.getTarget().getName() = "platform_device_put" and
      labeledRelease.getEnclosingFunction() = fn and
      labeledRelease.getLocation().getStartLine() > leakyReturn.getLocation().getStartLine()
    )
  )
}

from FunctionCall acquireCall, ReturnStmt leakyReturn
where isMissingPutOnErrorPath(acquireCall, leakyReturn)
select leakyReturn, "Memory leak: platform_device_alloc'd device is not released via platform_device_put before this error return; other error paths in the same function DO use platform_device_put, so this return likely should 'goto err' instead."
