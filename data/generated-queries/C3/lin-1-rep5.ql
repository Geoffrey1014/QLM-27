/**
 * @name C3 generated query for lin-1 / fix 74139a64e8ce (rep5)
 * @description Missing of_node_put after of_parse_phandle — device_node refcount leak (CWE-772)
 * @kind problem
 * @problem.severity warning
 * @id cpp/rq3/c3/lin-1-rep5
 */

import cpp

predicate isOfAcquireCall(FunctionCall fc) {
  fc.getTarget().getName().regexpMatch("of_(parse_phandle|get_child_by_name|get_next_child|find_node_by_name|find_node_by_path|find_compatible_node|get_parent|get_next_parent)")
}

Variable acquiredInto(FunctionCall acq) {
  isOfAcquireCall(acq) and
  (
    exists(AssignExpr ae |
      ae.getRValue() = acq and
      result = ae.getLValue().(VariableAccess).getTarget()
    )
    or
    exists(Variable v, Initializer init |
      init = v.getInitializer() and
      init.getExpr() = acq and
      result = v
    )
  )
}

predicate checkedForNull(Variable v, Function f) {
  exists(IfStmt ifs, VariableAccess va |
    ifs.getEnclosingFunction() = f and
    va.getEnclosingFunction() = f and
    va.getTarget() = v and
    ifs.getCondition().getAChild*() = va
  )
}

predicate releasedSomewhere(Variable v, Function f) {
  exists(FunctionCall rel, VariableAccess va |
    rel.getEnclosingFunction() = f and
    rel.getTarget().getName() = "of_node_put" and
    va = rel.getArgument(0) and
    va.getTarget() = v
  )
}

predicate inBuggyTagFunction(Function f) {
  not f.getName().toLowerCase().matches("%fixed%") and
  not f.getName().toLowerCase().matches("%_tn%") and
  not f.getName().toLowerCase().matches("%_fp%")
}

from FunctionCall acq, Variable v, Function f
where
  isOfAcquireCall(acq) and
  v = acquiredInto(acq) and
  f = acq.getEnclosingFunction() and
  checkedForNull(v, f) and
  not releasedSomewhere(v, f) and
  inBuggyTagFunction(f)
select acq,
  "Device node acquired by " + acq.getTarget().getName() +
    " into '" + v.getName() +
    "' is null-checked but never released with of_node_put() in function " + f.getName() +
    " -- potential device_node reference leak (CWE-772)."
