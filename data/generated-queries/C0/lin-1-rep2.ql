/**
 * @name Missing of_node_put on device_node acquired via of_parse_phandle family
 * @description A device_node pointer obtained from an of_parse_phandle-style API
 *              owns a reference that must be released with of_node_put() before
 *              the variable is reassigned, before the enclosing loop iteration
 *              ends without releasing, or before the function returns. Missing
 *              such a release is a refcount leak (CVE class).
 * @kind problem
 * @problem.severity warning
 * @id cpp/linux-of-node-leak-parse-phandle
 * @tags reliability
 *       correctness
 *       resource-leak
 *       linux-kernel
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph

/**
 * Functions in the of_* family that return a `struct device_node *` with a
 * refcount the caller must release via of_node_put().
 */
predicate isOfNodeAcquirer(Function f) {
  f.getName() in [
      "of_parse_phandle",
      "of_parse_phandle_with_args",
      "of_parse_phandle_with_fixed_args",
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
      "of_get_next_child",
      "of_get_next_available_child",
      "of_get_next_cpu_node",
      "of_get_cpu_node",
      "of_find_next_cache_node",
      "of_node_get"
    ]
}

/** A call that acquires a device_node reference. */
class AcquireCall extends FunctionCall {
  AcquireCall() { isOfNodeAcquirer(this.getTarget()) }
}

/** A call that releases a device_node reference. */
class ReleaseCall extends FunctionCall {
  ReleaseCall() {
    this.getTarget().getName() = "of_node_put"
    or
    // Common wrappers that internally drop the reference.
    this.getTarget().getName() in [
        "of_node_put_safe",
        "__free_device_node"
      ]
  }
}

/**
 * The local variable `v` is assigned the result of an acquire call `acq` at
 * statement `assignStmt`.
 */
predicate acquireAssignsLocal(AcquireCall acq, LocalVariable v, ControlFlowNode assignStmt) {
  exists(AssignExpr a |
    a.getLValue() = v.getAnAccess() and
    a.getRValue() = acq and
    assignStmt = a.getEnclosingStmt()
  )
  or
  exists(Initializer init |
    init.getDeclaration() = v and
    init.getExpr() = acq and
    assignStmt = acq
  )
}

/**
 * `rel` is a release call whose argument is an access to `v`.
 */
predicate releasesVar(ReleaseCall rel, LocalVariable v) {
  rel.getAnArgument() = v.getAnAccess()
}

/**
 * `n` is reachable from `start` via successor edges without passing through
 * a node that releases `v` or reassigns `v`.
 */
predicate reachableWithoutRelease(ControlFlowNode start, ControlFlowNode n, LocalVariable v) {
  n = start.getASuccessor() and
  not (exists(ReleaseCall rel | rel = n and releasesVar(rel, v))) and
  not (exists(AcquireCall acq2 | acquireAssignsLocal(acq2, v, n)))
  or
  exists(ControlFlowNode mid |
    reachableWithoutRelease(start, mid, v) and
    n = mid.getASuccessor() and
    not (exists(ReleaseCall rel | rel = n and releasesVar(rel, v))) and
    not (exists(AcquireCall acq2 | acquireAssignsLocal(acq2, v, n)))
  )
}

/**
 * From the acquire-assignment node `acqStmt` for variable `v`, there exists
 * a control-flow path to an exit / reassignment that never passes through a
 * release of `v`.
 */
predicate hasLeakingPath(ControlFlowNode acqStmt, LocalVariable v) {
  exists(ControlFlowNode n |
    reachableWithoutRelease(acqStmt, n, v) and
    (
      // exits the enclosing function without releasing
      n instanceof ReturnStmt
      or
      // reassigns v (overwrites the live reference)
      exists(AcquireCall acq2 | acquireAssignsLocal(acq2, v, n) and acq2 != acqStmt)
    )
  )
}

from AcquireCall acq, LocalVariable v, ControlFlowNode acqStmt, Function enclosing
where
  acquireAssignsLocal(acq, v, acqStmt) and
  enclosing = acq.getEnclosingFunction() and
  // The variable must be a device_node pointer (filters of_node_get-on-other-types FPs minimally).
  v.getType().getUnspecifiedType().(PointerType).getBaseType().getName() = "device_node" and
  hasLeakingPath(acqStmt, v)
select acq,
  "Device node acquired by '" + acq.getTarget().getName() +
    "' may leak: on some control-flow path the reference held by '" + v.getName() +
    "' is not released by of_node_put() before the variable is overwritten or the function returns."
