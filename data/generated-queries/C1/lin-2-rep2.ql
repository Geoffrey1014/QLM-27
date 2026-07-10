/**
 * @name Missing of_node_put after device-tree node acquisition
 * @description An of_*-family call returns a struct device_node* whose
 *              refcount has been incremented. If the enclosing function
 *              never calls of_node_put() on the variable that stores the
 *              result, the reference leaks (CWE-401).
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-lin-2
 */

import cpp

/* APIs that acquire a struct device_node* whose refcount must be released. */
predicate isOfAcquireApi(string name) {
  name = "of_parse_phandle" or
  name = "of_find_node_by_name" or
  name = "of_find_node_by_path" or
  name = "of_find_node_opts_by_path" or
  name = "of_find_matching_node" or
  name = "of_find_matching_node_and_match" or
  name = "of_find_compatible_node" or
  name = "of_get_child_by_name" or
  name = "of_get_next_child" or
  name = "of_get_next_available_child" or
  name = "of_get_parent" or
  name = "of_get_next_parent" or
  name = "of_get_cpu_node" or
  name = "of_irq_find_parent"
}

predicate isOfReleaseCall(FunctionCall c) {
  c.getTarget().getName() = "of_node_put"
}

/* Variable receiving call's return value, via init or assignment. */
Variable getReceiverVariable(FunctionCall call) {
  exists(Variable v |
    v.getInitializer().getExpr() = call and result = v
  )
  or
  exists(AssignExpr a |
    a.getRValue() = call and
    result = a.getLValue().(VariableAccess).getTarget()
  )
}

/* True if f calls of_node_put() with first argument reading v. */
predicate hasReleaseInFunction(Function f, Variable v) {
  exists(FunctionCall put, VariableAccess arg |
    isOfReleaseCall(put) and
    put.getEnclosingFunction() = f and
    arg = put.getArgument(0) and
    arg.getTarget() = v
  )
}

from FunctionCall acquire, Variable v, Function f
where
  isOfAcquireApi(acquire.getTarget().getName()) and
  v = getReceiverVariable(acquire) and
  f = acquire.getEnclosingFunction() and
  not hasReleaseInFunction(f, v)
select acquire,
  "Call to " + acquire.getTarget().getName() +
    " stores a refcounted device_node in '" + v.getName() +
    "' but the enclosing function never calls of_node_put() on it -- reference leak."
