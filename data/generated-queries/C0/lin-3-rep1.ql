/**
 * @name of_node refcount leak on early-return error path
 * @description A call to an of_* node-acquiring API (e.g. of_parse_phandle,
 *              of_find_node_by_name, of_get_child_by_name, of_get_parent, ...)
 *              returns a device_node with the refcount incremented. The caller
 *              must of_node_put() it on ALL paths once done. This query flags
 *              callers that may return (typically on an error of a subsequent
 *              call) without calling of_node_put() on the acquired node.
 * @kind problem
 * @problem.severity warning
 * @id cpp/of-node-refcount-leak-early-return
 * @tags reliability
 *       correctness
 *       resource-leak
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph

/** An of_* API that returns a device_node with refcount incremented. */
class OfNodeAcquire extends FunctionCall {
  OfNodeAcquire() {
    exists(string n | n = this.getTarget().getName() |
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
      n = "of_get_child_by_name" or
      n = "of_get_compatible_child" or
      n = "of_get_next_child" or
      n = "of_get_next_available_child" or
      n = "of_get_next_parent" or
      n = "of_get_parent" or
      n = "of_irq_find_parent"
    )
  }
}

/** A call that releases (puts) a device_node. */
predicate isOfNodePut(FunctionCall fc) {
  fc.getTarget().getName() = "of_node_put"
}

/**
 * The acquired node is stored in a local variable `v` immediately:
 *   v = of_parse_phandle(...);
 */
predicate acquiresInto(OfNodeAcquire acq, LocalVariable v) {
  exists(AssignExpr ae |
    ae.getRValue() = acq and
    ae.getLValue() = v.getAnAccess()
  )
  or
  v.getInitializer().getExpr() = acq
}

/** `of_node_put(v)` is called on the variable. */
predicate putsVar(LocalVariable v) {
  exists(FunctionCall put |
    isOfNodePut(put) and
    put.getArgument(0) = v.getAnAccess()
  )
}

/**
 * There exists a control-flow path from `acq` to a ReturnStmt without crossing
 * an `of_node_put(v)` call on the acquired variable `v`.
 */
predicate leaksOnPath(OfNodeAcquire acq, LocalVariable v, ReturnStmt ret) {
  acquiresInto(acq, v) and
  ret.getEnclosingFunction() = acq.getEnclosingFunction() and
  exists(ControlFlowNode n |
    n = ret and
    acq.getASuccessor+() = n
  ) and
  not exists(FunctionCall put |
    isOfNodePut(put) and
    put.getArgument(0) = v.getAnAccess() and
    acq.getASuccessor+() = put and
    put.getASuccessor+() = ret
  )
}

from OfNodeAcquire acq, LocalVariable v, ReturnStmt ret
where
  leaksOnPath(acq, v, ret) and
  // Only report when the function has multiple return paths (typical error-leak
  // shape) OR there is at least one early conditional return between acq and ret.
  exists(ReturnStmt other |
    other.getEnclosingFunction() = acq.getEnclosingFunction() and
    other != ret
  ) and
  // Avoid noise: require that some put exists in the function (so we don't flag
  // funcs that simply transfer ownership / never put).
  putsVar(v)
select acq,
  "of_* node-acquiring call returns a refcounted node stored in $@, but a return path at $@ may be reached without calling of_node_put() on it (refcount leak).",
  v, v.getName(), ret, "this return"
