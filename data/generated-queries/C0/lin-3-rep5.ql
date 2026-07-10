/**
 * @name Missing of_node_put after of_parse_phandle on error path
 * @description of_parse_phandle (and related of_* helpers) returns a device_node with
 *              its refcount incremented. The caller must call of_node_put() on every
 *              control-flow path. This query flags calls where the node escapes a
 *              function (return / dev_err_probe-style early-return) without a matching
 *              of_node_put() on at least one path.
 * @kind problem
 * @problem.severity warning
 * @id cpp/of-parse-phandle-refcount-leak
 * @tags reliability
 *       correctness
 *       refcount
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph

/**
 * Functions in the of_* family that acquire a `struct device_node *`
 * with an incremented refcount. Caller owns one reference and must release
 * it via `of_node_put` (or a sink that transfers ownership).
 */
predicate isOfNodeAcquire(Function f) {
  f.getName() in [
      "of_parse_phandle",
      "of_get_child_by_name",
      "of_get_next_child",
      "of_get_next_available_child",
      "of_get_parent",
      "of_get_next_parent",
      "of_find_node_by_name",
      "of_find_node_by_path",
      "of_find_node_by_phandle",
      "of_find_compatible_node",
      "of_find_matching_node",
      "of_find_matching_node_and_match",
      "of_find_node_with_property",
      "of_get_compatible_child"
    ]
}

/** A call to one of the of_* node-acquiring helpers. */
class OfAcquireCall extends FunctionCall {
  OfAcquireCall() { isOfNodeAcquire(this.getTarget()) }
}

/** A call that releases / transfers ownership of the node. */
predicate isReleaseCall(FunctionCall fc, Expr arg) {
  fc.getTarget().getName() = "of_node_put" and arg = fc.getArgument(0)
  or
  // some helpers consume ownership: of_node_put_kobj etc — kept narrow.
  fc.getTarget().getName() = "of_node_put_kobj" and arg = fc.getArgument(0)
}

/** Local variable that receives an of_* node refcount. */
class TrackedVar extends LocalVariable {
  OfAcquireCall acq;

  TrackedVar() {
    exists(AssignExpr ae |
      ae.getRValue() = acq and
      ae.getLValue() = this.getAnAccess()
    )
    or
    this.getInitializer().getExpr() = acq
  }

  OfAcquireCall getAcquire() { result = acq }
}

/**
 * A control-flow node where `v` is read by a release call.
 */
predicate releasedAt(TrackedVar v, ControlFlowNode n) {
  exists(FunctionCall fc, Expr arg |
    isReleaseCall(fc, arg) and
    arg = v.getAnAccess() and
    n = fc
  )
}

/**
 * A return statement reachable from the acquire `acq` of variable `v`
 * without an intervening of_node_put(v) on that path.
 */
predicate leakyReturn(TrackedVar v, OfAcquireCall acq, ReturnStmt ret) {
  acq = v.getAcquire() and
  acq.getEnclosingFunction() = ret.getEnclosingFunction() and
  exists(ControlFlowNode n |
    n = acq.getASuccessor+() and
    n = ret and
    not exists(ControlFlowNode rel |
      releasedAt(v, rel) and
      rel = acq.getASuccessor+() and
      rel.getASuccessor*() = n and
      // release dominates this particular path: ensure rel is between acq and ret
      acq.getASuccessor+() = rel
    )
  )
}

from TrackedVar v, OfAcquireCall acq, ReturnStmt ret
where
  leakyReturn(v, acq, ret) and
  // suppress trivially-released cases: there must exist at least one return path
  // on which no release happens between acq and that return.
  not exists(FunctionCall rel |
    isReleaseCall(rel, v.getAnAccess()) and
    rel.getEnclosingFunction() = acq.getEnclosingFunction() and
    // rel post-dominates acq (covers every exit path)
    forall(ReturnStmt r2 | r2.getEnclosingFunction() = acq.getEnclosingFunction() |
      acq.getASuccessor+() = rel and rel.getASuccessor*() = r2
    )
  )
select acq,
  "Node acquired by $@ may leak: variable '" + v.getName() +
    "' is not of_node_put() on the path to $@.",
  acq.getTarget(), acq.getTarget().getName(), ret, "this return"
