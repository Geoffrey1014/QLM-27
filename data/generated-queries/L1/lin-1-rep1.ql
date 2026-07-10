/**
 * @name Missing of_node_put after of_parse_phandle (device_node ref leak)
 * @description Detects device_node references acquired via of_parse_phandle
 *              that are stored in a local variable but never released with
 *              of_node_put on that same variable within the enclosing function.
 * @kind problem
 * @problem.severity warning
 * @id qlm/l1-lin1-of-parse-phandle-leak
 */
import cpp

predicate isAcquireCall(FunctionCall fc) {
  fc.getTarget().getName() = "of_parse_phandle"
}

from FunctionCall acquire, Function enclosing, Variable v
where isAcquireCall(acquire)
  and enclosing = acquire.getEnclosingFunction()
  and exists(AssignExpr ae |
    ae.getRValue() = acquire and
    ae.getLValue() = v.getAnAccess()
  )
  and not exists(FunctionCall release |
    release.getTarget().getName() = "of_node_put" and
    release.getEnclosingFunction() = enclosing and
    release.getAnArgument() = v.getAnAccess()
  )
select acquire,
  "Device node reference from of_parse_phandle assigned to '" + v.getName() +
  "' may be leaked in function '" + enclosing.getName() +
  "' (no of_node_put on this variable)."
