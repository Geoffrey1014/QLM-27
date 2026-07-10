/**
 * @name of_node_put missing on early-return error path
 * @description An of_*-family API returns a struct device_node* with an
 *              incremented refcount. The caller is required to release
 *              it via of_node_put() on every exit from the function.
 *              This query flags acquisitions where at least one return
 *              statement (e.g. an IS_ERR()-guarded early return) is
 *              reachable from the acquire site WITHOUT passing through
 *              any of_node_put() on the receiver variable -- the
 *              device-tree node is leaked on that path (CWE-401).
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-lin-3
 */

import cpp

/**
 * Linux of_* APIs that increment the refcount of the returned
 * device_node. Caller owns the reference and must release it via
 * of_node_put().
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

/** The Variable that captures the return value of `call`. */
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

/** A call to of_node_put whose first argument reads variable `v`. */
predicate isOfNodePutOf(FunctionCall put, Variable v) {
  put.getTarget().getName() = "of_node_put" and
  put.getArgument(0).(VariableAccess).getTarget() = v
}

from FunctionCall acquire, Variable recv, Function enclosing,
     ReturnStmt leakyReturn
where
  isOfNodeAcquireApi(acquire.getTarget().getName()) and
  recv = receiverVariableOf(acquire) and
  enclosing = acquire.getEnclosingFunction() and
  leakyReturn.getEnclosingFunction() = enclosing and
  // The return is reachable from the acquire's successor.
  acquire.getASuccessor+() = leakyReturn and
  // No of_node_put on `recv` lies on any path from the acquire to this return.
  not exists(FunctionCall put |
    isOfNodePutOf(put, recv) and
    acquire.getASuccessor+() = put and
    put.getASuccessor+() = leakyReturn
  )
select acquire,
  "Call to " + acquire.getTarget().getName() +
    " stores a refcounted device_node in '" + recv.getName() +
    "' but a return at $@ is reachable without a matching of_node_put() -- node leak on that path.",
  leakyReturn, "this exit"
