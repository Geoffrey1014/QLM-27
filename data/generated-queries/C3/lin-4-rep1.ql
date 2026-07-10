/**
 * @name Refcount leak on of_parse_phandle (four-features-Lin)
 * @description Detects functions that obtain a device_node via of_parse_phandle
 *              and then return on an error path without calling of_node_put on
 *              that node.
 * @kind problem
 * @problem.severity warning
 * @id qlm/refcount-leak-of-parse-phandle
 */

import cpp

predicate isAcquire(FunctionCall fc) {
  fc.getTarget().getName() = "of_parse_phandle"
}

predicate isRelease(FunctionCall fc, Variable v) {
  fc.getTarget().getName() = "of_node_put" and
  fc.getArgument(0) = v.getAnAccess()
}

predicate acquiresInto(FunctionCall fc, Variable v) {
  isAcquire(fc) and
  exists(AssignExpr a | a.getRValue() = fc and a.getLValue() = v.getAnAccess())
}

/* A return reachable in the CFG from the acquire without passing through a
   matching of_node_put on the same variable. */
predicate hasLeakingReturn(FunctionCall acq, Variable v, ReturnStmt ret) {
  acquiresInto(acq, v) and
  ret.getEnclosingFunction() = acq.getEnclosingFunction() and
  acq.getASuccessor+() = ret and
  not exists(FunctionCall rel |
    isRelease(rel, v) and
    acq.getASuccessor+() = rel and
    rel.getASuccessor+() = ret
  )
}

from FunctionCall acq, Variable v, ReturnStmt ret
where hasLeakingReturn(acq, v, ret)
select ret, "Potential refcount leak: " + acq.getTarget().getName() +
       " assigned to '" + v.getName() + "' in " +
       acq.getEnclosingFunction().getName() +
       " but no of_node_put before this return."
