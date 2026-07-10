/**
 * @name Missing of_node_put after of_parse_phandle (device_node refcount leak)
 * @description Detects functions that acquire a device_node via of_parse_phandle
 *              (storing the result into a local/parameter variable) but never
 *              call of_node_put on that variable within the same function.
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3/c3/lin-1-rep2
 */

import cpp

predicate isAcquireCall(FunctionCall fc) {
  fc.getTarget().getName() = "of_parse_phandle"
}

predicate isReleaseCallOn(FunctionCall fc, Variable v) {
  fc.getTarget().getName() = "of_node_put" and
  fc.getArgument(0) = v.getAnAccess()
}

predicate acquiredInto(FunctionCall fc, Variable v) {
  isAcquireCall(fc) and
  exists(AssignExpr a |
    a.getRValue() = fc and
    a.getLValue() = v.getAnAccess()
  )
}

predicate missingRelease(FunctionCall fc, Variable v) {
  acquiredInto(fc, v) and
  not exists(FunctionCall rel |
    isReleaseCallOn(rel, v) and
    rel.getEnclosingFunction() = fc.getEnclosingFunction()
  )
}

from FunctionCall acquire, Variable v
where missingRelease(acquire, v)
select acquire,
  "Resource acquired into $@ via " + acquire.getTarget().getName() +
    " without matching of_node_put in same function",
  v, v.getName()
