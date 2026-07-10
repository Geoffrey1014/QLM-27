/**
 * @name of_node_put placed after a conditional early return that skips it
 * @description An of_*-family call returns a struct device_node* whose
 *              refcount has been incremented. The caller stores the result
 *              in a variable and later releases it via of_node_put(). If a
 *              conditional `return` statement is positioned between the
 *              acquire and the release, the early-return path leaks the
 *              device-tree node reference (CWE-401).
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-lin-3
 */

import cpp

/**
 * APIs in the Linux of_* family that return a struct device_node* with
 * an incremented refcount; the caller must eventually call of_node_put().
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
 * Source-line of a Locatable, in its primary file.
 */
int startLineOf(Locatable l) {
  result = l.getLocation().getStartLine()
}

from
  FunctionCall acquire, Variable recv, Function enclosing,
  FunctionCall put, ReturnStmt earlyReturn
where
  isOfNodeAcquireApi(acquire.getTarget().getName()) and
  recv = receiverVariableOf(acquire) and
  enclosing = acquire.getEnclosingFunction() and
  // Some of_node_put(recv) exists in the same function -- so the developer
  // intended to release, but its placement is wrong.
  put.getTarget().getName() = "of_node_put" and
  put.getEnclosingFunction() = enclosing and
  exists(VariableAccess arg |
    arg = put.getArgument(0) and arg.getTarget() = recv
  ) and
  // An early return is sandwiched between the acquire and the release in
  // source order, AND that return is nested inside a conditional construct
  // (so the release path is conditionally skipped).
  earlyReturn.getEnclosingFunction() = enclosing and
  startLineOf(earlyReturn) > startLineOf(acquire) and
  startLineOf(earlyReturn) < startLineOf(put) and
  exists(IfStmt guard | earlyReturn.getParent*() = guard) and
  // Same source file (avoid cross-TU noise).
  acquire.getFile() = put.getFile() and
  acquire.getFile() = earlyReturn.getFile()
select acquire,
  "Refcount leak: " + acquire.getTarget().getName() +
    " stores a device_node in '" + recv.getName() +
    "'; a conditional early return at line " + startLineOf(earlyReturn).toString() +
    " can skip the of_node_put() at line " + startLineOf(put).toString() + "."
