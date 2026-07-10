/**
 * @name Missing of_node_put on error path after of_parse_phandle
 * @description of_parse_phandle (and related of_* node-acquiring siblings) returns a
 *              device_node pointer with its refcount incremented. If a subsequent call
 *              that uses the node can fail and the function returns on that error
 *              without calling of_node_put on the acquired node, the refcount is leaked.
 * @kind problem
 * @problem.severity warning
 * @id cpp/of-node-refcount-leak-error-path
 * @tags correctness
 *       reliability
 *       resource-leak
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph

/**
 * Functions in the `of_*` family that return a `device_node *` with the refcount
 * incremented and therefore obligate the caller to call `of_node_put` on the result.
 */
predicate isOfNodeAcquire(Function f) {
  f.getName() in [
      "of_parse_phandle",
      "of_parse_phandle_with_args",
      "of_parse_phandle_with_fixed_args",
      "of_find_node_by_name",
      "of_find_node_by_path",
      "of_find_node_by_phandle",
      "of_find_node_by_type",
      "of_find_compatible_node",
      "of_find_matching_node",
      "of_find_matching_node_and_match",
      "of_get_parent",
      "of_get_next_parent",
      "of_get_next_child",
      "of_get_next_available_child",
      "of_get_child_by_name",
      "of_get_compatible_child",
      "of_graph_get_next_endpoint",
      "of_graph_get_remote_endpoint",
      "of_graph_get_remote_node",
      "of_graph_get_remote_port_parent",
      "of_graph_get_remote_port",
      "of_graph_get_port_by_id",
      "of_irq_find_parent"
    ]
}

/** A call to a node-acquiring function whose result is stored in `v`. */
class AcquireCall extends FunctionCall {
  Variable v;

  AcquireCall() {
    isOfNodeAcquire(this.getTarget()) and
    exists(AssignExpr a |
      a.getRValue() = this and
      a.getLValue() = v.getAnAccess())
    or
    isOfNodeAcquire(this.getTarget()) and
    exists(Initializer i |
      i.getExpr() = this and
      i.getDeclaration() = v)
  }

  Variable getAcquiredVar() { result = v }
}

/** A call to `of_node_put` whose argument is an access to `v`. */
predicate isOfNodePutOf(FunctionCall fc, Variable v) {
  fc.getTarget().getName() = "of_node_put" and
  fc.getArgument(0) = v.getAnAccess()
}

/**
 * A `return` statement that is on an error path: it returns either an error pointer
 * (PTR_ERR/ERR_PTR/dev_err_probe), a negative integer literal, or NULL.
 */
predicate isErrorReturn(ReturnStmt r) {
  exists(Expr e | e = r.getExpr() |
    e.getValue().toInt() < 0
    or
    exists(FunctionCall fc | fc = e |
      fc.getTarget().getName() in [
          "PTR_ERR", "ERR_PTR", "ERR_CAST", "dev_err_probe", "ERR_PTR_PE"
        ])
    or
    // wrapped: return foo(PTR_ERR(...), ...)
    exists(FunctionCall fc | fc.getEnclosingStmt() = r |
      fc.getTarget().getName() = "dev_err_probe")
  )
  or
  // Any return whose expression mentions PTR_ERR or ERR_PTR transitively
  exists(FunctionCall inner |
    inner.getEnclosingStmt() = r and
    inner.getTarget().getName() in ["PTR_ERR", "ERR_PTR", "ERR_CAST", "dev_err_probe"]
  )
}

/**
 * Holds if there is an execution path from the acquire-call `ac` to the return
 * statement `ret` (in the same function) along which no `of_node_put(v)` is called,
 * where `v` is the variable holding the acquired node.
 */
predicate leakedOnPath(AcquireCall ac, ReturnStmt ret) {
  ac.getEnclosingFunction() = ret.getEnclosingFunction() and
  isErrorReturn(ret) and
  exists(ControlFlowNode n |
    n = ac.getASuccessor+() and
    n = ret
  ) and
  not exists(FunctionCall put |
    isOfNodePutOf(put, ac.getAcquiredVar()) and
    put = ac.getASuccessor+() and
    ret = put.getASuccessor+()
  )
}

from AcquireCall ac, ReturnStmt ret, Variable v
where
  v = ac.getAcquiredVar() and
  leakedOnPath(ac, ret) and
  // Exclude case where the variable is also stored long-term (e.g. into a struct field)
  // for later release; this is a coarse filter.
  not exists(AssignExpr a |
    a.getEnclosingFunction() = ac.getEnclosingFunction() and
    a.getRValue() = v.getAnAccess() and
    a.getLValue() instanceof FieldAccess
  )
select ac,
  "Possible refcount leak: '" + ac.getTarget().getName() +
    "' acquires device_node into '" + v.getName() +
    "' but no of_node_put on error-return path at $@.", ret, "this return"
