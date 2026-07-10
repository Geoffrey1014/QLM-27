/**
 * @name Missing of_node_put on early loop exit
 * @description Detects an of_parse_phandle() acquisition inside a loop where an
 *              early continue/break/return exit path may leave the returned
 *              device_node reference unreleased.
 * @kind problem
 * @problem.severity warning
 * @id qlm/l0/of-parse-phandle-leak
 */

import cpp

predicate isOfNodeAcquire(FunctionCall fc) {
  fc.getTarget().getName() = "of_parse_phandle"
}

predicate hasOfNodePut(Function f, Variable v) {
  exists(FunctionCall rel |
    rel.getEnclosingFunction() = f and
    rel.getTarget().getName() = "of_node_put" and
    rel.getAnArgument() = v.getAnAccess()
  )
}

from FunctionCall acquire, Variable v, Function f
where
  isOfNodeAcquire(acquire) and
  f = acquire.getEnclosingFunction() and
  (
    // captured by assignment: state_node = of_parse_phandle(...)
    exists(AssignExpr a |
      a.getRValue() = acquire and
      a.getLValue() = v.getAnAccess()
    )
    or
    // captured by initializer: struct device_node *n = of_parse_phandle(...)
    exists(Initializer init |
      init.getExpr() = acquire and
      init.getDeclaration() = v
    )
  ) and
  not hasOfNodePut(f, v)
select acquire,
  "of_parse_phandle result assigned to '" + v.getName() +
  "' but function has no of_node_put on it — possible device_node leak."
