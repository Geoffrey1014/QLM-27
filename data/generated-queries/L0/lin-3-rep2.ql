/**
 * @name device_node refcount leak after of_parse_phandle
 * @description Detects a call to of_parse_phandle whose returned device_node
 *              is assigned to a local variable and then followed by a return
 *              statement in the same function without an intervening
 *              of_node_put call on any variable — modelling the aries_wm8994
 *              pattern where the error path returns before the release.
 * @kind problem
 * @problem.severity warning
 * @id qlm/l0/lin-3-rep2/of-node-put-leak
 */
import cpp

predicate isDeviceNodeAcquire(FunctionCall fc) {
  fc.getTarget().getName() = "of_parse_phandle"
}

from FunctionCall acquire, LocalVariable v, Function enclosing, ReturnStmt r
where
  isDeviceNodeAcquire(acquire)
  and enclosing = acquire.getEnclosingFunction()
  and v.getAnAssignedValue() = acquire
  and r.getEnclosingFunction() = enclosing
  and acquire.getLocation().getStartLine() < r.getLocation().getStartLine()
  and not exists(FunctionCall put |
        put.getTarget().getName() = "of_node_put"
        and put.getEnclosingFunction() = enclosing
        and put.getLocation().getStartLine() < r.getLocation().getStartLine()
        and put.getLocation().getStartLine() > acquire.getLocation().getStartLine())
select acquire,
  "device_node from of_parse_phandle may leak on an error return before of_node_put"
