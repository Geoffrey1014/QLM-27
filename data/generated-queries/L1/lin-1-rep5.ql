/**
 * @name Missing of_node_put for of_parse_phandle result
 * @description Detects a function that acquires a device_node reference via
 *              of_parse_phandle() and assigns it to a local variable, but
 *              never invokes of_node_put() on that variable, indicating a
 *              potential device_node reference leak.
 * @kind problem
 * @problem.severity warning
 * @id qlm/l1/of-parse-phandle-leak
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
    exists(AssignExpr a |
      a.getRValue() = acquire and
      a.getLValue() = v.getAnAccess()
    )
    or
    exists(Initializer init |
      init.getExpr() = acquire and
      init.getDeclaration() = v
    )
  ) and
  not hasOfNodePut(f, v)
select acquire,
  "of_parse_phandle result assigned to '" + v.getName() +
  "' but function has no of_node_put on it - possible device_node leak."
