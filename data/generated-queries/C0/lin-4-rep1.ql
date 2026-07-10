/**
 * @name Missing of_node_put on error path after of_parse_phandle
 * @description An OF device node obtained from of_parse_phandle (or its siblings
 *   such as of_find_node_by_name, of_get_child_by_name, of_get_parent, etc.)
 *   has its refcount incremented and must be released with of_node_put() on all
 *   exit paths. Missing of_node_put() on an error/return path causes a refcount
 *   leak (device-tree node leak).
 * @kind problem
 * @problem.severity warning
 * @id cpp/of-node-refcount-leak
 * @tags reliability
 *       correctness
 *       resource-leak
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph

/**
 * Functions that acquire an `of_node` reference (refcount++) and return it.
 * Caller is responsible for releasing with of_node_put().
 */
predicate isOfNodeAcquire(Function f) {
  f.getName() in [
      "of_parse_phandle",
      "of_find_node_by_name",
      "of_find_node_by_path",
      "of_find_node_by_phandle",
      "of_find_node_by_type",
      "of_find_compatible_node",
      "of_find_matching_node",
      "of_find_matching_node_and_match",
      "of_get_parent",
      "of_get_next_parent",
      "of_get_child_by_name",
      "of_get_compatible_child",
      "of_get_next_child",
      "of_get_next_available_child",
      "of_get_cpu_node",
      "of_cpu_device_node_get",
      "of_graph_get_next_endpoint",
      "of_graph_get_remote_endpoint",
      "of_graph_get_remote_node",
      "of_graph_get_remote_port",
      "of_graph_get_remote_port_parent",
      "of_graph_get_port_by_id",
      "of_irq_find_parent"
    ]
}

/** The release routine that decrements the refcount. */
predicate isOfNodeRelease(FunctionCall fc, Expr node) {
  fc.getTarget().getName() = "of_node_put" and
  fc.getArgument(0) = node
}

/**
 * Holds if `v` is assigned the result of an of_node-acquiring call at `acq`.
 */
predicate acquiresInto(LocalVariable v, FunctionCall acq) {
  isOfNodeAcquire(acq.getTarget()) and
  (
    // direct assignment: v = of_parse_phandle(...);
    exists(AssignExpr a |
      a.getLValue() = v.getAnAccess() and
      a.getRValue() = acq
    )
    or
    // initializer at declaration: struct device_node *v = of_parse_phandle(...);
    v.getInitializer().getExpr() = acq
  )
}

/**
 * Holds if some call to of_node_put() (or equivalent release) is reachable
 * from `acq` on `v` along some path. We check structural existence within the
 * enclosing function — purely syntactic / intraprocedural overapproximation.
 */
predicate hasReleaseOn(LocalVariable v, FunctionCall acq) {
  exists(FunctionCall rel |
    rel.getEnclosingFunction() = acq.getEnclosingFunction() and
    rel.getTarget().getName() = "of_node_put" and
    rel.getArgument(0) = v.getAnAccess()
  )
}

/**
 * Holds if there is a `return` statement reachable from `acq` (in the same
 * function) that is NOT preceded by a `of_node_put(v)` along that path.
 * We approximate "not preceded" with: there exists a return whose path from
 * `acq` does not pass through any of_node_put on v.
 */
predicate hasReturnWithoutRelease(LocalVariable v, FunctionCall acq, ReturnStmt ret) {
  ret.getEnclosingFunction() = acq.getEnclosingFunction() and
  acq.getASuccessor+() = ret and
  not exists(FunctionCall rel |
    rel.getEnclosingFunction() = acq.getEnclosingFunction() and
    rel.getTarget().getName() = "of_node_put" and
    rel.getArgument(0) = v.getAnAccess() and
    acq.getASuccessor+() = rel and
    rel.getASuccessor+() = ret
  )
}

from LocalVariable v, FunctionCall acq, ReturnStmt ret
where
  acquiresInto(v, acq) and
  v.getType().getUnspecifiedType().(PointerType).getBaseType().getName() = "device_node" and
  // there must be at least one release somewhere (otherwise too noisy / a different bug class)
  hasReleaseOn(v, acq) and
  hasReturnWithoutRelease(v, acq, ret)
select ret,
  "Possible refcount leak: device_node $@ acquired by $@ may be returned without of_node_put().",
  v, v.getName(), acq, acq.getTarget().getName()
