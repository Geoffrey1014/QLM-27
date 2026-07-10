/**
 * @name pm_runtime_get_sync without pm_runtime_put on error path
 * @description pm_runtime_get_sync() (and siblings) increment the usage counter
 *              even when they fail. If the caller takes an error/early-return
 *              path without calling pm_runtime_put(), the runtime PM reference
 *              count leaks. This query detects callers that check the return
 *              value of a pm_runtime_get* function, branch on failure, and
 *              return without releasing the reference.
 * @kind problem
 * @problem.severity warning
 * @id cpp/pm-runtime-get-sync-refcount-leak
 * @tags reliability
 *       correctness
 *       resource-leak
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph

/**
 * A call to a pm_runtime_get* function whose return value, on failure
 * (negative), still leaves the usage counter incremented and therefore
 * requires a matching pm_runtime_put*() in the error path.
 */
class PmRuntimeGetCall extends FunctionCall {
  PmRuntimeGetCall() {
    exists(string n | n = this.getTarget().getName() |
      n = "pm_runtime_get_sync" or
      n = "pm_runtime_get_sync_suspend" or
      n = "pm_runtime_resume_and_get" or
      n = "__pm_runtime_resume" or
      n = "pm_runtime_get" or
      n = "pm_runtime_get_noresume"
    )
  }

  /** The device argument passed to this call. */
  Expr getDeviceArg() { result = this.getArgument(0) }
}

/**
 * A call to a pm_runtime_put* function that releases the runtime PM
 * reference acquired by a pm_runtime_get* call.
 */
class PmRuntimePutCall extends FunctionCall {
  PmRuntimePutCall() {
    exists(string n | n = this.getTarget().getName() |
      n = "pm_runtime_put" or
      n = "pm_runtime_put_sync" or
      n = "pm_runtime_put_noidle" or
      n = "pm_runtime_put_autosuspend" or
      n = "pm_runtime_put_sync_autosuspend" or
      n = "pm_runtime_put_sync_suspend" or
      n = "__pm_runtime_put_autosuspend"
    )
  }

  Expr getDeviceArg() { result = this.getArgument(0) }
}

/**
 * Holds if `e` syntactically references the same device expression as `d`
 * (a textual match on the source text; deliberately conservative so we
 * don't require full dataflow on a kernel-scale DB).
 */
predicate sameDeviceExpr(Expr a, Expr b) {
  a.toString() = b.toString()
}

/**
 * Holds if there is a basic-block-reachable path from `get` to a
 * `return` statement that goes through an error check on `get`'s
 * return value, but no pm_runtime_put* on the same device appears
 * between `get` and the return.
 */
predicate missingPutOnErrorPath(PmRuntimeGetCall get, ReturnStmt ret) {
  // The return is reachable from the get's enclosing statement.
  get.getEnclosingFunction() = ret.getEnclosingFunction() and
  // The error branch: there exists an `if` whose condition mentions
  // a comparison of (something flowing from) get with a negative
  // constant or zero, and the return is inside that if-then.
  exists(IfStmt ifs, Expr cond |
    cond = ifs.getCondition() and
    ifs.getEnclosingFunction() = get.getEnclosingFunction() and
    // condition syntactically mentions a "<" against 0 (the canonical
    // `if (ret < 0)` shape) — keep loose to catch variants.
    (
      cond.toString().matches("%< 0%") or
      cond.toString().matches("%<0%") or
      cond.toString().matches("%IS_ERR%")
    ) and
    ret.getParent*() = ifs.getThen()
  ) and
  // No pm_runtime_put* on the same device sits between the get and
  // the return inside the same function.
  not exists(PmRuntimePutCall put |
    put.getEnclosingFunction() = get.getEnclosingFunction() and
    sameDeviceExpr(put.getDeviceArg(), get.getDeviceArg()) and
    put.getLocation().getStartLine() > get.getLocation().getStartLine() and
    put.getLocation().getStartLine() <= ret.getLocation().getStartLine()
  )
}

from PmRuntimeGetCall get, ReturnStmt ret
where
  missingPutOnErrorPath(get, ret) and
  // Exclude trivial cases where the enclosing function itself is a
  // pm_runtime_* helper / wrapper (those legitimately propagate the
  // counter state).
  not get.getEnclosingFunction().getName().matches("pm_runtime_%") and
  not get.getEnclosingFunction().getName().matches("%_runtime_resume") and
  not get.getEnclosingFunction().getName().matches("%_runtime_suspend")
select get,
  "Call to " + get.getTarget().getName() +
    "() may leak a runtime-PM reference: the error path returning at $@ does not call pm_runtime_put*.",
  ret, "this return"
