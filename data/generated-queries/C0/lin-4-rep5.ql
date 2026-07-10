/**
 * @name Missing of_node_put on error paths after of_parse_phandle family
 * @description of_parse_phandle and siblings return a device_node with an incremented
 *              refcount. The caller must invoke of_node_put() on every path that leaves
 *              the scope where the node is live, including early error returns. Missing
 *              an of_node_put on an error path leaks the refcount.
 * @kind problem
 * @problem.severity warning
 * @id cpp/of-node-refcount-leak-error-path
 * @tags reliability
 *       correctness
 *       resource-leak
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph

/**
 * Functions that return a device_node* with refcount incremented.
 * Caller must call of_node_put() on the returned node.
 */
predicate isOfNodeAcquirer(Function f) {
  f.getName() in [
      "of_parse_phandle",
      "of_get_child_by_name",
      "of_get_next_child",
      "of_get_next_available_child",
      "of_get_next_cpu_node",
      "of_get_compatible_child",
      "of_find_node_by_name",
      "of_find_node_by_path",
      "of_find_node_by_phandle",
      "of_find_compatible_node",
      "of_find_matching_node",
      "of_find_matching_node_and_match",
      "of_find_node_with_property",
      "of_find_node_by_type",
      "of_get_parent",
      "of_get_next_parent",
      "of_irq_find_parent",
      "of_cpu_device_node_get"
    ]
}

/**
 * Holds if `call` is a call to an of-node acquiring function whose result
 * is bound to a local variable `v`.
 */
predicate acquireAssignedToLocal(FunctionCall call, LocalVariable v) {
  isOfNodeAcquirer(call.getTarget()) and
  (
    // direct initializer: struct device_node *np = of_parse_phandle(...);
    v.getInitializer().getExpr() = call
    or
    // assignment: np = of_parse_phandle(...);
    exists(AssignExpr a |
      a.getRValue() = call and
      a.getLValue() = v.getAnAccess()
    )
  )
}

/**
 * Holds if there is a call to of_node_put(v) somewhere in the same function.
 */
predicate hasOfNodePutOn(LocalVariable v, Function f) {
  exists(FunctionCall put |
    put.getEnclosingFunction() = f and
    put.getTarget().getName() = "of_node_put" and
    put.getArgument(0) = v.getAnAccess()
  )
}

/**
 * Holds if there is an early `return` statement in `f` that returns an error
 * (i.e. a non-zero / negative integer or an error pointer) following the
 * acquisition `call` but does NOT pass through any of_node_put on `v` reachable
 * from the call.
 *
 * Approximated structurally: a ReturnStmt inside the function whose source
 * location is after the acquire call, whose returned expression is a
 * recognisable error value, with no of_node_put(v) call lexically between the
 * acquire and the return on the same path.
 */
predicate hasErrorReturnWithoutPut(FunctionCall call, LocalVariable v, ReturnStmt ret) {
  exists(Function f |
    call.getEnclosingFunction() = f and
    ret.getEnclosingFunction() = f and
    ret.getLocation().getStartLine() > call.getLocation().getStartLine() and
    // returned value is "errorish": a negative integer literal, a unary minus
    // on an identifier (e.g. -ENOMEM), or an ERR_PTR call.
    exists(Expr e | e = ret.getExpr() |
      e instanceof Literal and e.getValue().toInt() < 0
      or
      e.(UnaryMinusExpr).getOperand() instanceof Expr
      or
      exists(FunctionCall errPtr |
        errPtr = e and errPtr.getTarget().getName() = "ERR_PTR"
      )
    ) and
    // no of_node_put(v) lies textually between the acquire and this return
    not exists(FunctionCall put |
      put.getEnclosingFunction() = f and
      put.getTarget().getName() = "of_node_put" and
      put.getArgument(0) = v.getAnAccess() and
      put.getLocation().getStartLine() >= call.getLocation().getStartLine() and
      put.getLocation().getStartLine() <= ret.getLocation().getStartLine()
    )
  )
}

from FunctionCall call, LocalVariable v, ReturnStmt ret, Function f
where
  acquireAssignedToLocal(call, v) and
  f = call.getEnclosingFunction() and
  // some put exists somewhere — meaning the developer is aware the node owns a refcount,
  // but at least one error path skips it. This greatly reduces FPs from cases where
  // the API does not actually require a put in this caller.
  hasOfNodePutOn(v, f) and
  hasErrorReturnWithoutPut(call, v, ret)
select ret,
  "Possible refcount leak: '" + v.getName() + "' obtained from $@ is not released by of_node_put() before this error return.",
  call, call.getTarget().getName()
