/**
 * @name C3 generated query for lin-1 / fix 74139a64e8ce (rep4)
 * @description Missing of_node_put after of_parse_phandle — device_node refcount leak (CWE-401)
 * @kind problem
 * @problem.severity warning
 * @id cpp/rq3/c3/lin-1-rep4
 */

import cpp

predicate acquiresDeviceNode(FunctionCall fc) {
  fc.getTarget().getName() in [
    "of_parse_phandle", "of_find_node_by_name", "of_find_node_by_path",
    "of_get_child_by_name", "of_find_compatible_node", "of_get_next_child"
  ]
}

predicate isReleaseCall(FunctionCall fc) {
  fc.getTarget().getName() = "of_node_put"
}

Variable boundVar(FunctionCall acquire) {
  exists(AssignExpr a |
    a.getRValue() = acquire and
    result = a.getLValue().(VariableAccess).getTarget()
  )
  or
  exists(Variable v |
    v.getInitializer().getExpr() = acquire and
    result = v
  )
}

predicate releasedInSameFn(FunctionCall acquire, Variable v) {
  exists(FunctionCall release, VariableAccess va |
    isReleaseCall(release) and
    release.getEnclosingFunction() = acquire.getEnclosingFunction() and
    va = release.getArgument(0) and
    va.getTarget() = v
  )
}

predicate guardedByNullCheck(FunctionCall acquire, Variable v) {
  exists(IfStmt ifs, VariableAccess va |
    ifs.getEnclosingFunction() = acquire.getEnclosingFunction() and
    va.getTarget() = v and
    ifs.getCondition().getAChild*() = va
  )
}

predicate inFixedVariant(FunctionCall fc) {
  fc.getEnclosingFunction().getName().toLowerCase().matches("%fixed%")
}

from FunctionCall acquire, Variable v
where
  acquiresDeviceNode(acquire) and
  v = boundVar(acquire) and
  guardedByNullCheck(acquire, v) and
  not releasedInSameFn(acquire, v) and
  not inFixedVariant(acquire)
select acquire,
  "Device node from " + acquire.getTarget().getName() +
  " bound to '" + v.getName() +
  "' is never released via of_node_put() — refcount leak"
