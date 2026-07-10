/**
 * @name Refcount leak: of_parse_phandle without of_node_put on error return
 * @description Detects functions where of_parse_phandle acquires a device_node
 *              reference but an intermediate error path returns without calling
 *              of_node_put on the acquired variable, leaking the refcount.
 * @kind problem
 * @problem.severity warning
 * @id qlm/l1-lin4-of-parse-phandle-leak
 */

import cpp

predicate isPhandleAcquire(FunctionCall fc) {
  fc.getTarget().getName() = "of_parse_phandle"
}

predicate hasNoPutOnErrorReturn(FunctionCall acquire, Variable v, ReturnStmt ret) {
  isPhandleAcquire(acquire) and
  exists(Function fn |
    fn = acquire.getEnclosingFunction() and
    ret.getEnclosingFunction() = fn and
    v.getAnAssignedValue() = acquire and
    exists(ret.getExpr()) and
    not exists(FunctionCall put |
      put.getTarget().getName() = "of_node_put" and
      put.getEnclosingFunction() = fn and
      put.getAnArgument().(VariableAccess).getTarget() = v and
      put.getLocation().getStartLine() < ret.getLocation().getStartLine() and
      put.getLocation().getStartLine() > acquire.getLocation().getStartLine()
    )
  )
}

from FunctionCall acquire, Variable v, ReturnStmt ret
where isPhandleAcquire(acquire)
  and hasNoPutOnErrorReturn(acquire, v, ret)
select acquire, "Refcount leak: of_parse_phandle result may not be released on error return at $@", ret, ret.toString()
