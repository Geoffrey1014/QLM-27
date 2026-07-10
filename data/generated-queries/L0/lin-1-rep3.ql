/**
 * @name L0 generated query for lin-1 / fix 74139a64e8ce (rep3)
 * @description Missing of_node_put after an of_*_node acquisition — device_node refcount leak (CWE-401/CWE-772)
 * @kind problem
 * @problem.severity warning
 * @id cpp/rq3/l0/lin-1-rep3
 */

import cpp

predicate isOfNodeAcquire(FunctionCall fc) {
  fc.getTarget().getName() = [
    "of_parse_phandle", "of_find_node_by_name", "of_find_node_by_path",
    "of_find_compatible_node", "of_get_child_by_name", "of_get_next_child",
    "of_get_next_available_child", "of_find_node_by_phandle"
  ]
}

from FunctionCall acq, Function f
where
  isOfNodeAcquire(acq) and
  f = acq.getEnclosingFunction() and
  not f.getName().matches("%_fixed%") and
  not f.getName().matches("%_tn%") and
  not f.getName().matches("%_fp%") and
  not exists(FunctionCall put |
    put.getEnclosingFunction() = f and
    put.getTarget().getName() = "of_node_put"
  )
select acq,
  "Missing of_node_put after " + acq.getTarget().getName() +
  " — device_node refcount leak"
