/**
 * @name Missing of_node_put after of_find_* function call
 * @description Detects cases where of_find_compatible_node() or similar functions
 *              return a device_node pointer with incremented refcount, but
 *              of_node_put() is never called to release it. This causes a
 *              reference count leak.
 *              Pattern from Linux commit 0f83e6b4161617014017a694888dd8743f46f071.
 * @kind problem
 * @problem.severity warning
 * @precision high
 * @id cpp/missing-of-node-put
 * @tags reliability
 *       security
 *       external/cwe/cwe-911
 */

import cpp

/**
 * A call to of_find_* functions that return a device_node pointer with
 * incremented refcount. The caller must call of_node_put() to release it.
 */
class OfFindCall extends FunctionCall {
  OfFindCall() {
    this.getTarget().hasName([
      "of_find_compatible_node",
      "of_find_node_by_name",
      "of_find_node_by_path",
      "of_find_node_by_phandle",
      "of_find_node_by_type",
      "of_find_matching_node",
      "of_find_matching_node_and_match",
      "of_find_node_opts_by_path",
      "of_find_node_with_property",
      "of_find_all_nodes"
    ])
  }
}

/**
 * A call to of_node_put that releases a reference.
 */
class OfNodePutCall extends FunctionCall {
  OfNodePutCall() {
    this.getTarget().hasName("of_node_put")
  }
}

/**
 * Holds if variable `v` is assigned the result of an of_find_* call.
 */
predicate isAssignedFromOfFind(Variable v, OfFindCall findCall) {
  exists(AssignExpr assign |
    assign.getRValue() = findCall and
    assign.getLValue().(VariableAccess).getTarget() = v
  )
  or
  exists(Initializer init |
    init.getExpr() = findCall and
    init.getDeclaration() = v
  )
}

/**
 * Holds if there's an of_node_put call for variable `v` in the function.
 */
predicate hasOfNodePutForVar(Variable v, Function f) {
  exists(OfNodePutCall putCall |
    putCall.getEnclosingFunction() = f and
    putCall.getAnArgument().(VariableAccess).getTarget() = v
  )
}

/**
 * Holds if variable `v` is reassigned after the of_find_* call but before
 * of_node_put is called - this means the original reference is lost.
 */
predicate isReassignedBeforePut(Variable v, OfFindCall findCall, Function f) {
  exists(AssignExpr reassign |
    reassign.getLValue().(VariableAccess).getTarget() = v and
    reassign.getEnclosingFunction() = f and
    // The reassignment is after the of_find call
    reassign.getLocation().getStartLine() > findCall.getLocation().getStartLine() and
    // And it's another of_find call (common pattern of reusing np variable)
    reassign.getRValue() instanceof OfFindCall and
    // Check if there's no of_node_put between the original find and the reassignment
    not exists(OfNodePutCall putCall |
      putCall.getEnclosingFunction() = f and
      putCall.getAnArgument().(VariableAccess).getTarget() = v and
      putCall.getLocation().getStartLine() > findCall.getLocation().getStartLine() and
      putCall.getLocation().getStartLine() < reassign.getLocation().getStartLine()
    )
  )
}

/**
 * Main query: Find of_find_* calls where the returned node is not released.
 */
from OfFindCall findCall, Variable nodeVar, Function f
where
  f = findCall.getEnclosingFunction() and
  isAssignedFromOfFind(nodeVar, findCall) and
  (
    // Case 1: No of_node_put at all for this variable in the function
    not hasOfNodePutForVar(nodeVar, f)
    or
    // Case 2: Variable is reassigned with another of_find before of_node_put
    isReassignedBeforePut(nodeVar, findCall, f)
  )
select findCall,
  "Potential refcount leak: " + findCall.getTarget().getName() + "() returns a node with " +
  "incremented refcount stored in '" + nodeVar.getName() + "', but of_node_put() is not called " +
  "to release it in function '" + f.getName() + "'."
