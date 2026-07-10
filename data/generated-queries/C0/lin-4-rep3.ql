/**
 * @name Missing of_node_put on of_* node-acquiring API result
 * @description Functions in the of_parse_phandle family return a device_node
 *              with its refcount incremented. The caller must drop the
 *              reference via of_node_put() on every path that leaves the
 *              variable's scope, including error paths and early returns.
 *              Missing of_node_put causes a refcount/resource leak.
 * @kind problem
 * @problem.severity warning
 * @id cpp/of-node-refcount-leak
 * @tags correctness
 *       reliability
 *       refcount-leak
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph

/**
 * Functions in the device-tree API that return a `struct device_node *`
 * with an incremented refcount, requiring a matching of_node_put().
 */
predicate isOfNodeAcquire(Function f) {
  exists(string n | n = f.getName() |
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
    n = "of_get_next_child" or
    n = "of_get_next_available_child" or
    n = "of_get_compatible_child" or
    n = "of_get_child_by_name" or
    n = "of_get_cpu_node" or
    n = "of_irq_find_parent"
  )
}

/** A call to an of_* node-acquiring function. */
class OfAcquireCall extends FunctionCall {
  OfAcquireCall() { isOfNodeAcquire(this.getTarget()) }
}

/**
 * The variable that receives the acquired node, either by direct
 * assignment `np = of_parse_phandle(...)` or initialization
 * `struct device_node *np = of_parse_phandle(...)`.
 */
predicate acquiredInto(OfAcquireCall call, Variable v) {
  exists(Assignment a |
    a.getRValue() = call and
    a.getLValue() = v.getAnAccess()
  )
  or
  v.getInitializer().getExpr() = call
}

/** A call to of_node_put on the variable `v`. */
predicate releasesVar(FunctionCall fc, Variable v) {
  fc.getTarget().getName() = "of_node_put" and
  fc.getArgument(0) = v.getAnAccess()
}

/**
 * The variable is "consumed" by being stored into a structure field or
 * passed to a function that takes ownership (heuristic: any non-of_node_put
 * call that takes the variable). We do NOT treat these as a release, but
 * we use it to avoid flagging "stash into struct" patterns where the
 * lifecycle is intentionally extended.
 */
predicate isStoredIntoStruct(Variable v) {
  exists(Assignment a |
    a.getRValue() = v.getAnAccess() and
    a.getLValue() instanceof FieldAccess
  )
}

/**
 * A return statement in the function that contains `call`, reachable from
 * `call`, on which no of_node_put(v) is executed between `call` and the
 * return.
 */
predicate leakingReturn(OfAcquireCall call, Variable v, ReturnStmt ret) {
  acquiredInto(call, v) and
  ret.getEnclosingFunction() = call.getEnclosingFunction() and
  // Reachability from the acquire call to the return.
  call.getAPredecessor*() = call and
  call.getASuccessor+() = ret and
  // No of_node_put(v) on the path between call and return.
  not exists(FunctionCall put |
    releasesVar(put, v) and
    put.getEnclosingFunction() = call.getEnclosingFunction() and
    call.getASuccessor+() = put and
    put.getASuccessor+() = ret
  )
}

from OfAcquireCall call, Variable v, ReturnStmt ret, Function f
where
  f = call.getEnclosingFunction() and
  acquiredInto(call, v) and
  leakingReturn(call, v, ret) and
  // Require at least one of_node_put(v) somewhere in the function — this
  // indicates the developer's intent that v IS reference-counted and must
  // be put. Filters out "stashed into struct, freed elsewhere" cases.
  exists(FunctionCall put |
    releasesVar(put, v) and put.getEnclosingFunction() = f
  ) and
  // Exclude cases where the node is stored into a struct field (ownership
  // transfer).
  not isStoredIntoStruct(v)
select ret,
  "Possible refcount leak: device_node acquired by $@ into '" + v.getName() +
    "' is not released by of_node_put() on this return path.",
  call, call.getTarget().getName()
