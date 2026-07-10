/**
 * @name Missing of_node_put on of_parse_phandle result before early return
 * @description of_parse_phandle (and sibling of_* node-acquiring APIs) return
 *              a device_node pointer with its refcount incremented. Every
 *              control-flow path that ends the function without storing the
 *              node into a refcount-managing structure must call of_node_put
 *              on it. If a function returns (often on an error path) without
 *              first calling of_node_put, the node refcount leaks.
 * @kind problem
 * @problem.severity warning
 * @id cpp/of-node-refcount-leak
 * @tags reliability
 *       correctness
 *       resource-leak
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph
import semmle.code.cpp.dataflow.DataFlow

/**
 * Functions that return a `struct device_node *` whose reference count is
 * incremented and must be released with `of_node_put`.
 */
predicate isOfNodeAcquirer(Function f) {
  exists(string n | n = f.getName() |
    n = "of_parse_phandle" or
    n = "of_parse_phandle_with_args" or
    n = "of_parse_phandle_with_fixed_args" or
    n = "of_get_child_by_name" or
    n = "of_get_compatible_child" or
    n = "of_get_next_child" or
    n = "of_get_next_available_child" or
    n = "of_get_next_cpu_node" or
    n = "of_get_parent" or
    n = "of_get_next_parent" or
    n = "of_find_node_by_name" or
    n = "of_find_node_by_path" or
    n = "of_find_node_by_phandle" or
    n = "of_find_node_by_type" or
    n = "of_find_compatible_node" or
    n = "of_find_matching_node" or
    n = "of_find_matching_node_and_match" or
    n = "of_find_node_with_property" or
    n = "of_node_get" or
    n = "of_cpu_device_node_get" or
    n = "of_graph_get_next_endpoint" or
    n = "of_graph_get_remote_endpoint" or
    n = "of_graph_get_remote_port" or
    n = "of_graph_get_remote_port_parent" or
    n = "of_graph_get_endpoint_by_regs" or
    n = "of_graph_get_remote_node"
  )
}

/** Functions that release a device_node reference (consume the +1 ref). */
predicate isOfNodeReleaser(Function f) {
  exists(string n | n = f.getName() |
    n = "of_node_put" or
    n = "of_clk_del_provider"
  )
}

/**
 * Holds if `call` is a call to an acquirer whose returned node is bound to
 * local variable `v` in function `enclosing`.
 */
predicate acquiredInto(FunctionCall call, Variable v, Function enclosing) {
  isOfNodeAcquirer(call.getTarget()) and
  enclosing = call.getEnclosingFunction() and
  exists(AssignExpr ae |
    ae.getRValue() = call and
    ae.getLValue() = v.getAnAccess()
  )
  or
  isOfNodeAcquirer(call.getTarget()) and
  enclosing = call.getEnclosingFunction() and
  exists(Initializer init |
    init.getExpr() = call and
    init.getDeclaration() = v
  )
}

/**
 * Holds if `n` is a control-flow node (in the same function that acquired
 * `v` via `acq`) that reads `v` and passes it to a releaser, or that
 * stores `v` into a longer-lived structure (escapes ownership).
 */
predicate consumesNode(ControlFlowNode n, Variable v) {
  // Pass to of_node_put or similar releaser.
  exists(FunctionCall fc |
    fc = n and
    isOfNodeReleaser(fc.getTarget()) and
    fc.getAnArgument() = v.getAnAccess()
  )
  or
  // Escape: passed as argument to any other function call (assumed to take
  // ownership or to itself release on its error path). This is a deliberate
  // under-approximation to keep FPs low — we ONLY treat the node as consumed
  // if it is passed to a function that is NOT a releaser AND the result is
  // stored, OR it is stored into a struct field. The simplest sound-ish
  // approximation: any FieldAccess assignment with v on RHS.
  exists(AssignExpr ae, FieldAccess fa |
    ae.getLValue() = fa and
    ae.getRValue() = v.getAnAccess() and
    n = ae
  )
}

/**
 * Holds if a return statement `ret` in function `f` is reachable from `call`
 * without an intervening consumer of `v`.
 */
predicate reachesReturnWithoutRelease(FunctionCall call, Variable v, ReturnStmt ret) {
  acquiredInto(call, v, ret.getEnclosingFunction()) and
  call.getASuccessor+() = ret and
  not exists(ControlFlowNode mid |
    consumesNode(mid, v) and
    call.getASuccessor+() = mid and
    mid.getASuccessor+() = ret
  )
}

from FunctionCall call, Variable v, ReturnStmt ret, Function enclosing
where
  acquiredInto(call, v, enclosing) and
  reachesReturnWithoutRelease(call, v, ret) and
  // Exclude the trivial case where the acquirer's result is the return value.
  not exists(ReturnStmt rret |
    rret = ret and
    rret.getExpr() = v.getAnAccess()
  )
select call,
  "Node acquired by $@ (stored in '" + v.getName() +
    "') may leak: return at $@ has no intervening of_node_put on this variable.",
  call.getTarget(), call.getTarget().getName(),
  ret, "this return"
