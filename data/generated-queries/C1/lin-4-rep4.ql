/**
 * @name Refcount leak on error return after of_* phandle acquisition
 * @description An of_* helper returns a struct device_node* whose refcount
 *              has been incremented; the caller must release it via
 *              of_node_put(). If a control-flow path from the acquiring
 *              call reaches a ReturnStmt without an intervening
 *              of_node_put() on the receiving variable, the refcount
 *              leaks (CWE-401).
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-lin-4
 * @tags reliability
 *       refcount
 */

import cpp

/**
 * Linux of_* helpers that return a refcounted struct device_node* and
 * therefore obligate the caller to balance with of_node_put().
 */
predicate ofNodeAcquireFn(string n) {
  n = "of_parse_phandle" or
  n = "of_parse_phandle_with_args" or
  n = "of_parse_phandle_with_fixed_args" or
  n = "of_find_node_by_name" or
  n = "of_find_node_by_path" or
  n = "of_find_node_by_phandle" or
  n = "of_find_node_by_type" or
  n = "of_find_compatible_node" or
  n = "of_find_matching_node" or
  n = "of_find_matching_node_and_match" or
  n = "of_find_node_with_property" or
  n = "of_get_parent" or
  n = "of_get_next_parent" or
  n = "of_get_child_by_name" or
  n = "of_get_next_child" or
  n = "of_get_next_available_child" or
  n = "of_get_next_cpu_node" or
  n = "of_get_compatible_child" or
  n = "of_get_cpu_node" or
  n = "of_graph_get_next_endpoint" or
  n = "of_graph_get_remote_endpoint" or
  n = "of_graph_get_remote_node" or
  n = "of_graph_get_remote_port" or
  n = "of_graph_get_remote_port_parent" or
  n = "of_graph_get_port_by_id" or
  n = "of_irq_find_parent"
}

/** A call to of_node_put(v) inside `f`. */
predicate releasesNode(Function f, Variable v) {
  exists(FunctionCall put, VariableAccess va |
    put.getEnclosingFunction() = f and
    put.getTarget().getName() = "of_node_put" and
    va = put.getArgument(0) and
    va.getTarget() = v
  )
}

/**
 * `recv` is the local variable that receives the result of `acq` --
 * either through initialization `T *v = acq(...)` or through a
 * subsequent assignment `v = acq(...)`.
 */
predicate receivesAcquire(Variable recv, FunctionCall acq) {
  exists(Initializer init |
    init.getDeclaration() = recv and
    init.getExpr() = acq
  )
  or
  exists(AssignExpr a, VariableAccess lhs |
    a.getRValue() = acq and
    lhs = a.getLValue() and
    lhs.getTarget() = recv
  )
}

/**
 * True if there exists a control-flow path acq -> ret that does NOT
 * pass through any of_node_put(recv) along the way.
 */
predicate leakingReturn(FunctionCall acq, Variable recv, ReturnStmt ret, Function f) {
  ofNodeAcquireFn(acq.getTarget().getName()) and
  receivesAcquire(recv, acq) and
  acq.getEnclosingFunction() = f and
  ret.getEnclosingFunction() = f and
  acq.getASuccessor+() = ret and
  not exists(FunctionCall put |
    put.getEnclosingFunction() = f and
    put.getTarget().getName() = "of_node_put" and
    put.getArgument(0).(VariableAccess).getTarget() = recv and
    acq.getASuccessor+() = put and
    put.getASuccessor+() = ret
  )
}

from FunctionCall acq, Variable recv, ReturnStmt ret, Function f
where
  leakingReturn(acq, recv, ret, f) and
  // The enclosing function calls of_node_put on recv on at least one
  // path; pure "never released" cases are reported by a complementary
  // check. This focuses on missing-release-on-error-return bugs of the
  // kind seen in the lin-4 seed.
  releasesNode(f, recv) and
  // Skip ownership-transfer cases (of_node_get reseats the refcount).
  not exists(FunctionCall xfer |
    xfer.getEnclosingFunction() = f and
    xfer.getTarget().getName() = "of_node_get" and
    xfer.getArgument(0).(VariableAccess).getTarget() = recv
  ) and
  // Exclude returns inside the null-check guard of `recv` itself
  // (the acquirer returned NULL so there is no refcount to release).
  // We exclude returns lexically nested in an IfStmt whose condition
  // tests `recv` (e.g. `if (!recv) return -E...;`).
  not exists(IfStmt ifs, VariableAccess cond |
    ifs.getEnclosingFunction() = f and
    cond.getParent*() = ifs.getCondition() and
    cond.getTarget() = recv and
    ret.getParent*() = ifs.getThen()
  )
select ret,
  "Refcount leak: device_node acquired by $@ may not be released on this return path (variable '" +
    recv.getName() + "').",
  acq, acq.getTarget().getName()
