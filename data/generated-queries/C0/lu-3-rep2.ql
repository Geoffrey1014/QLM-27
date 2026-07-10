/**
 * @name pm_runtime_get_sync reference count leak on error path
 * @description pm_runtime_get_sync() increments the runtime PM usage counter even
 *              when it returns an error. Returning directly on (ret < 0) without
 *              calling pm_runtime_put()/pm_runtime_put_noidle() leaks the refcount.
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
 * Calls to the pm_runtime_get_sync family. These all increment the runtime PM
 * usage counter on entry regardless of whether they ultimately return an error.
 * `pm_runtime_resume_and_get` is the modern API that does the put-on-error for you,
 * so it is intentionally NOT included.
 */
class PmRuntimeGetSyncCall extends FunctionCall {
  PmRuntimeGetSyncCall() {
    exists(string n | n = this.getTarget().getName() |
      n = "pm_runtime_get_sync" or
      n = "pm_runtime_get" or
      n = "pm_runtime_get_noresume"
    )
  }
}

/**
 * A call that releases a runtime-PM reference previously taken by
 * pm_runtime_get_sync (or siblings).
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
}

/**
 * Holds if `e` is (or contains) a comparison testing that the value of `getCall`
 * is negative (i.e. an error: `ret < 0`, `ret != 0` after a get_sync assignment,
 * or the call result used directly as `pm_runtime_get_sync(...) < 0`).
 */
predicate isErrorTest(Expr e, PmRuntimeGetSyncCall getCall, LocalScopeVariable retVar) {
  // Pattern A: ret = pm_runtime_get_sync(dev); if (ret < 0) { ... }
  exists(RelationalOperation rel, VariableAccess va |
    rel = e and
    va = rel.getAnOperand() and
    va.getTarget() = retVar and
    rel.getAnOperand().getValue().toInt() = 0 and
    exists(AssignExpr ae |
      ae.getLValue().(VariableAccess).getTarget() = retVar and
      ae.getRValue() = getCall
    )
  )
  or
  // Pattern B: if (pm_runtime_get_sync(dev) < 0) { ... }
  exists(RelationalOperation rel |
    rel = e and
    rel.getAnOperand() = getCall and
    rel.getAnOperand().getValue().toInt() = 0 and
    retVar = retVar // retVar irrelevant in this pattern; bind a dummy below
  )
}

/**
 * Holds if the basic block `bb` (an error-handling block reached when get_sync
 * returned < 0) contains a pm_runtime_put-family call before exiting.
 */
predicate blockHasPutBeforeReturn(BasicBlock bb) {
  exists(PmRuntimePutCall p | p.getEnclosingFunction() = bb.getEnclosingFunction() and
    p.getBasicBlock() = bb)
  or
  // Or a successor reachable without going through another get_sync.
  exists(BasicBlock succ, PmRuntimePutCall p |
    bb.getASuccessor+() = succ and
    p.getBasicBlock() = succ and
    p.getEnclosingFunction() = bb.getEnclosingFunction()
  )
}

from
  PmRuntimeGetSyncCall getCall, Function f, IfStmt ifs, ReturnStmt ret
where
  f = getCall.getEnclosingFunction() and
  ifs.getEnclosingFunction() = f and
  ret.getEnclosingFunction() = f and
  // The if-statement tests an error result of the get_sync call.
  (
    // Pattern A: assigned to a variable.
    exists(LocalScopeVariable v, AssignExpr ae, VariableAccess va, RelationalOperation rel |
      ae.getRValue() = getCall and
      ae.getLValue().(VariableAccess).getTarget() = v and
      rel = ifs.getCondition().getAChild*() and
      va = rel.getAnOperand() and
      va.getTarget() = v and
      rel.getAnOperand().getValue().toInt() = 0
    )
    or
    // Pattern B: call appears directly in the condition.
    exists(RelationalOperation rel |
      rel = ifs.getCondition().getAChild*() and
      rel.getAnOperand() = getCall and
      rel.getAnOperand().getValue().toInt() = 0
    )
  ) and
  // The if-then branch returns (an error path) without calling pm_runtime_put.
  ret.getEnclosingStmt+() = ifs.getThen() and
  not exists(PmRuntimePutCall p |
    p.getEnclosingStmt+() = ifs.getThen()
  ) and
  // The get_sync call lexically precedes the if-statement.
  getCall.getLocation().getStartLine() <= ifs.getLocation().getStartLine()
select ifs,
  "Error path after $@ returns without calling pm_runtime_put(), leaking the runtime-PM refcount.",
  getCall, getCall.getTarget().getName()
