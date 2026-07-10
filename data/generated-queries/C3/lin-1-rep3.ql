/**
 * @name C3 generated query for lin-1 / fix 74139a64e8ce (rep3)
 * @description Missing of_node_put after an of_*_node acquisition — device_node refcount leak (CWE-401/CWE-772)
 * @kind problem
 * @problem.severity warning
 * @id cpp/rq3/c3/lin-1-rep3
 */

import cpp

predicate isOfNodeAcquire(FunctionCall fc) {
  fc.getTarget().getName() = [
    "of_parse_phandle", "of_find_node_by_name", "of_find_node_by_path",
    "of_find_compatible_node", "of_get_child_by_name", "of_get_next_child",
    "of_get_next_available_child", "of_find_node_by_phandle"
  ]
}

Variable acquireTargetVar(FunctionCall acq) {
  isOfNodeAcquire(acq) and
  (
    exists(AssignExpr a | a.getRValue() = acq and result.getAnAccess() = a.getLValue())
    or
    exists(Variable v | v.getInitializer().getExpr() = acq and result = v)
  )
}

predicate hasOfNodePutOn(Function f, Variable v) {
  exists(FunctionCall put, VariableAccess va |
    put.getEnclosingFunction() = f and
    put.getTarget().getName() = "of_node_put" and
    va = put.getArgument(0) and
    va.getTarget() = v
  )
}

predicate hasNullGuard(Function f, Variable v) {
  exists(IfStmt ifs, VariableAccess va |
    ifs.getEnclosingFunction() = f and
    va.getTarget() = v and
    ifs.getCondition().getAChild*() = va
  )
}

predicate isInFixedVariant(FunctionCall fc) {
  exists(string n | n = fc.getEnclosingFunction().getName() |
    n.matches("%_fixed%") or n.matches("%_tn%") or n.matches("%_fp%")
  )
}

from FunctionCall acq, Variable v, Function f
where
  isOfNodeAcquire(acq) and
  v = acquireTargetVar(acq) and
  f = acq.getEnclosingFunction() and
  hasNullGuard(f, v) and
  not hasOfNodePutOn(f, v) and
  not isInFixedVariant(acq)
select acq,
  "Missing of_node_put on '" + v.getName() + "' acquired by " +
  acq.getTarget().getName() + " — device_node refcount leak"
