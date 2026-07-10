/**
 * @name Missing of_node_put on device_node reference returned by of_parse_phandle-family API
 * @description Calls in the `of_*` family (e.g. of_parse_phandle, of_find_*,
 *              of_get_*) return a `struct device_node *` whose reference
 *              count has been incremented and that must be balanced with
 *              of_node_put(). If the enclosing function stores the result
 *              in a local variable and never invokes of_node_put() on it
 *              along any path, the node reference leaks (CWE-401, CWE-772).
 *              This monolithic detector reports each such acquire site.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-lin-1
 */

import cpp

/* ----- Acquire / release API surface ------------------------------- */

predicate isOfAcquireApi(string n) {
  n = "of_parse_phandle" or
  n = "of_parse_phandle_with_args" or
  n = "of_parse_phandle_with_fixed_args" or
  n = "of_find_node_by_name" or
  n = "of_find_node_by_path" or
  n = "of_find_node_opts_by_path" or
  n = "of_find_node_by_phandle" or
  n = "of_find_matching_node" or
  n = "of_find_matching_node_and_match" or
  n = "of_find_compatible_node" or
  n = "of_get_child_by_name" or
  n = "of_get_next_child" or
  n = "of_get_next_available_child" or
  n = "of_get_parent" or
  n = "of_get_next_parent" or
  n = "of_get_cpu_node" or
  n = "of_irq_find_parent"
}

predicate isOfReleaseApi(string n) {
  n = "of_node_put"
}

/* The local Variable that receives the return value of `acq`, whether via
 * declaration-with-initializer or plain assignment. */
Variable receiverOf(FunctionCall acq) {
  exists(Variable v |
    v.getInitializer().getExpr() = acq and result = v
  )
  or
  exists(AssignExpr a |
    a.getRValue() = acq and
    result = a.getLValue().(VariableAccess).getTarget()
  )
}

/* Does function `f` contain *any* of_node_put(arg) where `arg` reads `v`? */
predicate releasedSomewhereIn(Function f, Variable v) {
  exists(FunctionCall put |
    isOfReleaseApi(put.getTarget().getName()) and
    put.getEnclosingFunction() = f and
    put.getArgument(0).(VariableAccess).getTarget() = v
  )
}

from FunctionCall acq, Function f, Variable v, string apiName
where
  apiName = acq.getTarget().getName() and
  isOfAcquireApi(apiName) and
  f = acq.getEnclosingFunction() and
  v = receiverOf(acq) and
  not releasedSomewhereIn(f, v)
select acq,
  "Call to " + apiName + " returns a refcounted device_node stored in '" +
    v.getName() +
    "', but the enclosing function never releases it with of_node_put() — possible reference leak."
