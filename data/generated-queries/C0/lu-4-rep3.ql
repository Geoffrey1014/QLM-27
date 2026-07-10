/**
 * @name Missing platform_device_put on error path after platform_device_alloc
 * @description After calling platform_device_alloc(), the returned device must be
 *              released via platform_device_put() on every error path before the
 *              device is registered. A direct `return` from an error branch that
 *              skips the cleanup label leaks the allocated platform_device.
 * @kind problem
 * @problem.severity warning
 * @id cpp/missing-platform-device-put-on-error
 * @tags correctness
 *       reliability
 *       memory-leak
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph
import semmle.code.cpp.dataflow.DataFlow

/**
 * A call that acquires a platform_device-like resource which must later be
 * released with `*_put` (or freed via a labeled cleanup path).
 */
class AllocCall extends FunctionCall {
  AllocCall() {
    this.getTarget().getName() = "platform_device_alloc"
  }
}

/** A call that releases the resource produced by an `AllocCall`. */
class ReleaseCall extends FunctionCall {
  ReleaseCall() {
    this.getTarget().getName() = "platform_device_put"
  }
}

/**
 * Holds if `alloc` flows (directly or via a field store like `dwc->dwc3 = ...`)
 * to the argument of some release call somewhere in the same function.
 * Used only to make sure we are looking at a function that *does* have a
 * cleanup path -- the bug is that one error branch SKIPS it.
 */
predicate functionHasReleasePath(Function f, AllocCall alloc) {
  alloc.getEnclosingFunction() = f and
  exists(ReleaseCall rel | rel.getEnclosingFunction() = f)
}

/**
 * A "checked call" sitting between the alloc and the function exit: a call
 * whose return value is tested and, on failure, leads to an early `return`
 * that does NOT pass through any `ReleaseCall`.
 */
predicate leakyErrorReturn(
  AllocCall alloc, FunctionCall checked, ReturnStmt ret, Function f
) {
  functionHasReleasePath(f, alloc) and
  checked.getEnclosingFunction() = f and
  ret.getEnclosingFunction() = f and
  // The checked call happens after the alloc, lexically.
  alloc.getLocation().getStartLine() < checked.getLocation().getStartLine() and
  // The return happens after the checked call.
  checked.getLocation().getStartLine() <= ret.getLocation().getStartLine() and
  // The return is reachable from the checked call (same basic-block region).
  exists(IfStmt ifs |
    ifs.getEnclosingFunction() = f and
    ifs.getLocation().getStartLine() >= checked.getLocation().getStartLine() and
    ifs.getLocation().getStartLine() <= ret.getLocation().getStartLine() and
    // The condition tests the result of `checked` (heuristic: checked call is
    // inside the if's condition, or its result is assigned just before).
    (
      checked.getParent*() = ifs.getCondition()
      or
      exists(Variable v, AssignExpr a |
        a.getLValue().(VariableAccess).getTarget() = v and
        a.getRValue() = checked and
        ifs.getCondition().getAChild*().(VariableAccess).getTarget() = v
      )
    ) and
    ret.getParent*() = ifs.getThen()
  ) and
  // No ReleaseCall sits between the checked call and the return on this path.
  not exists(ReleaseCall rel |
    rel.getEnclosingFunction() = f and
    rel.getLocation().getStartLine() >= checked.getLocation().getStartLine() and
    rel.getLocation().getStartLine() <= ret.getLocation().getStartLine()
  ) and
  // Exclude the obvious case where the alloc itself failed (the very first
  // NULL-check on the alloc result is allowed to `return` without cleanup).
  checked != alloc and
  not checked.getTarget() = alloc.getTarget()
}

from AllocCall alloc, FunctionCall checked, ReturnStmt ret, Function f
where
  leakyErrorReturn(alloc, checked, ret, f) and
  // Filter: the checked call should be one of the typical "post-alloc setup"
  // calls that can fail -- platform_device_add_*, devm_*, of_*, etc.
  (
    checked.getTarget().getName().matches("platform_device_add%") or
    checked.getTarget().getName().matches("platform_device_set%") or
    checked.getTarget().getName().matches("device_add_%") or
    checked.getTarget().getName().matches("dev_pm_%")
  )
select ret,
  "Early return on error from $@ leaks platform_device allocated by $@ in function '" +
    f.getName() + "' (no platform_device_put on this path).",
  checked, checked.getTarget().getName(),
  alloc, "platform_device_alloc"
