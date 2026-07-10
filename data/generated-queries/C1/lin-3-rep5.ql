/**
 * @name Missing of_node_put on early-return path after device-tree acquire
 * @description An of_*-family API returns a struct device_node* whose
 *              refcount has been incremented. The caller must release
 *              the reference via of_node_put() on every path that exits
 *              the enclosing function. This query reports cases where an
 *              of_node_put() exists somewhere in the function but at
 *              least one return statement is CFG-reachable from the
 *              acquire without an intervening of_node_put() on the
 *              acquired variable -- i.e., an error-path refcount leak
 *              (CWE-401 / CWE-772).
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-lin-3
 */

import cpp

/**
 * Linux of_* APIs that return a struct device_node* with an incremented
 * refcount; the caller must release via of_node_put().
 */
predicate isOfNodeAcquireApi(string name) {
  name = "of_parse_phandle" or
  name = "of_parse_phandle_with_args" or
  name = "of_parse_phandle_with_fixed_args" or
  name = "of_find_node_by_name" or
  name = "of_find_node_by_path" or
  name = "of_find_node_opts_by_path" or
  name = "of_find_node_by_phandle" or
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

/** A call to of_node_put(). */
predicate isOfNodePut(FunctionCall c) {
  c.getTarget().getName() = "of_node_put"
}

/**
 * The local Variable that captures the return value of `call`, either
 * by initialization (`T *v = call(...);`) or assignment (`v = call();`).
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

/** True if `c` is a call to of_node_put() whose argument reads `v`. */
predicate isOfNodePutOn(FunctionCall c, Variable v) {
  isOfNodePut(c) and
  exists(VariableAccess a |
    a = c.getArgument(0) and a.getTarget() = v
  )
}

/**
 * True if there exists a CFG path from the acquire call `acq` to the
 * return statement `ret` (both in function `f`) that does NOT pass
 * through any of_node_put() on the acquired variable `v`.
 */
predicate unreleasedReturnPath(FunctionCall acq, Variable v, Function f, ReturnStmt ret) {
  acq.getEnclosingFunction() = f and
  ret.getEnclosingFunction() = f and
  exists(ControlFlowNode cur |
    cur = acq.getASuccessor+() and
    cur = ret and
    not exists(FunctionCall put |
      put = acq.getASuccessor+() and
      ret = put.getASuccessor+() and
      isOfNodePutOn(put, v)
    )
  )
}

from FunctionCall acquire, Variable recv, Function enclosing, ReturnStmt leakingRet
where
  isOfNodeAcquireApi(acquire.getTarget().getName()) and
  recv = receiverVariableOf(acquire) and
  enclosing = acquire.getEnclosingFunction() and
  // Function does call of_node_put on this variable somewhere (otherwise
  // it is a coarser "never released" bug, out of scope for this query --
  // it is detected by a sibling C1 query).
  exists(FunctionCall anyPut |
    anyPut.getEnclosingFunction() = enclosing and
    isOfNodePutOn(anyPut, recv)
  ) and
  // But there exists at least one return path that bypasses the put.
  unreleasedReturnPath(acquire, recv, enclosing, leakingRet)
select acquire,
  "Call to " + acquire.getTarget().getName() +
    " stores a refcounted device_node in '" + recv.getName() +
    "' but a return at $@ is reachable without an intervening of_node_put() -- error-path refcount leak.",
  leakingRet, "this return"
