/**
 * @name of_parse_phandle result missing of_node_put on error return (L1)
 * @description Detects a call to of_parse_phandle whose returned device_node
 *              is assigned to a local variable and is followed by a return
 *              statement in the same function without an intervening
 *              of_node_put on that variable — modelling the aries_wm8994
 *              refcount-leak pattern where the error path returns before
 *              the release.
 * @kind problem
 * @problem.severity warning
 * @id qlm/l1/of-parse-phandle-leak-lin-3-rep2
 */

import cpp

predicate isDeviceNodeAcquire(FunctionCall fc) {
  fc.getTarget().getName() = "of_parse_phandle"
}

predicate hasDeviceNodeRelease(Function f, Variable v) {
  exists(FunctionCall rel |
    rel.getEnclosingFunction() = f and
    rel.getTarget().getName() = "of_node_put" and
    rel.getArgument(0) = v.getAnAccess()
  )
}

from FunctionCall acquire, Variable v, Function f, ReturnStmt ret
where
  isDeviceNodeAcquire(acquire) and
  acquire.getEnclosingFunction() = f and
  v.getAnAssignedValue() = acquire and
  ret.getEnclosingFunction() = f and
  ret.getLocation().getStartLine() > acquire.getLocation().getStartLine() and
  not exists(FunctionCall rel |
    rel.getEnclosingFunction() = f and
    rel.getTarget().getName() = "of_node_put" and
    rel.getArgument(0) = v.getAnAccess() and
    rel.getLocation().getStartLine() > acquire.getLocation().getStartLine() and
    rel.getLocation().getStartLine() < ret.getLocation().getStartLine()
  )
select acquire,
  "device_node from of_parse_phandle assigned to $@ may leak on the error return at line " +
    ret.getLocation().getStartLine().toString(),
  v, v.getName()
