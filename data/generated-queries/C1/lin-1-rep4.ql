/**
 * @name Missing of_node_put after device-tree node acquisition
 * @description An of_*-family call returns a struct device_node* whose
 *              refcount has been incremented. If the enclosing function
 *              never releases the reference via of_node_put() on the
 *              variable receiving the result, the device-tree node
 *              reference leaks (CWE-401).
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-lin-1
 */

import cpp

/**
 * APIs in the Linux of_* family that return a struct device_node* with
 * an incremented refcount. The caller is responsible for releasing the
 * reference via of_node_put().
 */
predicate isOfNodeAcquireApi(string name) {
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

/** True if `c` is a call to of_node_put(). */
predicate isOfNodePut(FunctionCall c) {
  c.getTarget().getName() = "of_node_put"
}

/**
 * The Variable that captures the return value of `call`, either via
 * initialization (`T *v = call(...)`) or via assignment
 * (`v = call(...)`).
 */
Variable receiverVariableOf(FunctionCall call) {
  exists(Variable v |
    v.getInitializer().getExpr() = call and
    result = v
  )
  or
  exists(AssignExpr a, VariableAccess lhs |
    a.getRValue() = call and
    lhs = a.getLValue() and
    result = lhs.getTarget()
  )
}

/**
 * True iff some of_node_put() inside `f` takes a read of `v` as its
 * first argument.
 */
predicate releasesVariable(Function f, Variable v) {
  exists(FunctionCall put, VariableAccess arg |
    isOfNodePut(put) and
    put.getEnclosingFunction() = f and
    arg = put.getArgument(0) and
    arg.getTarget() = v
  )
}

from FunctionCall acquire, Variable recv, Function enclosing
where
  isOfNodeAcquireApi(acquire.getTarget().getName()) and
  recv = receiverVariableOf(acquire) and
  enclosing = acquire.getEnclosingFunction() and
  not releasesVariable(enclosing, recv)
select acquire,
  "Call to " + acquire.getTarget().getName() +
    " stores a refcounted device_node in '" + recv.getName() +
    "' but the enclosing function never calls of_node_put() on it -- reference leak."
