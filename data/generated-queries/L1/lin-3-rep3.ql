/**
 * @name Missing of_node_put after of_parse_phandle (device_node refcount leak)
 * @description Detects a call to of_parse_phandle whose result is assigned
 *              to a local variable but no of_node_put is called on that
 *              variable in the same enclosing function. Compositional L1
 *              configuration (<=2 predicates, compile self-fix only,
 *              POC pair-wise oracle OFF).
 * @kind problem
 * @problem.severity warning
 * @id qlm/l1/of-parse-phandle-leak-lin-3-rep3
 */

import cpp

predicate isAcquire(FunctionCall fc) {
  fc.getTarget().getName() = "of_parse_phandle"
}

predicate hasReleaseOn(Function f, Variable v) {
  exists(FunctionCall rel |
    rel.getEnclosingFunction() = f and
    rel.getTarget().getName() = "of_node_put" and
    rel.getArgument(0) = v.getAnAccess()
  )
}

from FunctionCall acquire, Variable v, Function f
where
  isAcquire(acquire) and
  v.getAnAssignedValue() = acquire and
  acquire.getEnclosingFunction() = f and
  not hasReleaseOn(f, v)
select acquire,
  "of_parse_phandle result assigned to $@ but no of_node_put in the same function",
  v, v.getName()
