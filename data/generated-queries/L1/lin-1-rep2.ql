/**
 * @name of_parse_phandle result missing of_node_put (L1)
 * @description Detects a call to of_parse_phandle whose result is assigned
 *              to a local variable but no of_node_put is called on that
 *              variable in the same function. Compositional two-predicate
 *              (L1) configuration with compile self-fix loop.
 * @kind problem
 * @problem.severity warning
 * @id qlm/l1/of-parse-phandle-leak-lin-1-rep2
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
