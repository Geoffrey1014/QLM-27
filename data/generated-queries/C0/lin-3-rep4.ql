/**
 * @name Refcount leak from of_* node-acquiring family on error path
 * @description A device_node pointer obtained from an of_* node-acquiring API
 *              (e.g. of_parse_phandle, of_find_node_by_*, of_get_*_node) carries
 *              an incremented refcount and must be released with of_node_put().
 *              If a subsequent consumer call returns an error and the function
 *              returns without calling of_node_put() on the acquired node, the
 *              node refcount leaks.
 * @kind problem
 * @problem.severity warning
 * @id cpp/of-node-refcount-leak-on-error
 * @tags reliability
 *       correctness
 *       resource-leak
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph

/** Holds if `name` is an of_* API that returns a device_node with an incremented refcount. */
predicate isOfNodeAcquirer(string name) {
  name = "of_parse_phandle" or
  name = "of_parse_phandle_with_args" or
  name = "of_parse_phandle_with_fixed_args" or
  name = "of_find_node_by_name" or
  name = "of_find_node_by_path" or
  name = "of_find_node_by_phandle" or
  name = "of_find_node_by_type" or
  name = "of_find_compatible_node" or
  name = "of_find_matching_node" or
  name = "of_find_matching_node_and_match" or
  name = "of_find_node_with_property" or
  name = "of_find_node_by_phandle" or
  name = "of_get_parent" or
  name = "of_get_next_parent" or
  name = "of_get_next_child" or
  name = "of_get_next_available_child" or
  name = "of_get_compatible_child" or
  name = "of_get_child_by_name" or
  name = "of_get_cpu_node" or
  name = "of_graph_get_next_endpoint" or
  name = "of_graph_get_remote_endpoint" or
  name = "of_graph_get_remote_port" or
  name = "of_graph_get_remote_port_parent" or
  name = "of_graph_get_remote_node" or
  name = "of_graph_get_endpoint_by_regs" or
  name = "of_irq_find_parent"
}

/** A call to an of_* node-acquiring API. */
class OfAcquireCall extends FunctionCall {
  OfAcquireCall() { isOfNodeAcquirer(this.getTarget().getName()) }
}

/** A call to of_node_put. */
class OfNodePutCall extends FunctionCall {
  OfNodePutCall() { this.getTarget().getName() = "of_node_put" }
}

/** Holds if `e` syntactically references the local variable `v`. */
predicate refsVar(Expr e, LocalVariable v) {
  exists(VariableAccess va | va = e.getAChild*() and va.getTarget() = v)
}

/** Holds if `c` calls of_node_put on (an expression referencing) variable `v`. */
predicate putsVar(OfNodePutCall c, LocalVariable v) {
  refsVar(c.getArgument(0), v)
}

/**
 * A return statement that, on its path from `acq`, exits the enclosing function
 * without an of_node_put on `v` having been executed on that path.
 */
predicate leakyReturn(OfAcquireCall acq, LocalVariable v, ReturnStmt ret) {
  // The acquire writes the node into v.
  exists(Assignment a |
    a.getRValue() = acq and
    a.getLValue().(VariableAccess).getTarget() = v
  ) and
  // ret is in the same function as acq.
  ret.getEnclosingFunction() = acq.getEnclosingFunction() and
  // There is a CFG path from the acquire to the return.
  acq.getASuccessor+() = ret and
  // No of_node_put on v on the way between the acquire and the return.
  not exists(OfNodePutCall put |
    putsVar(put, v) and
    acq.getASuccessor+() = put and
    put.getASuccessor+() = ret
  )
}

from OfAcquireCall acq, LocalVariable v, ReturnStmt ret, Function f
where
  f = acq.getEnclosingFunction() and
  leakyReturn(acq, v, ret) and
  // Filter: the function does call of_node_put on v somewhere (so the developer
  // recognized the need to release it) — this catches the "release on success
  // but not on error path" bug class while suppressing functions that
  // legitimately transfer ownership of the node out.
  exists(OfNodePutCall put | putsVar(put, v) and put.getEnclosingFunction() = f) and
  // Suppress functions that simply return the acquired node (ownership transfer).
  not exists(ReturnStmt r |
    r.getEnclosingFunction() = f and
    refsVar(r.getExpr(), v)
  )
select ret,
  "Possible refcount leak: device_node acquired by $@ may not be released by of_node_put() before this return.",
  acq, acq.getTarget().getName()
