/**
 * @name Missing pm_runtime_put on pm_runtime_get_sync failure
 * @description pm_runtime_get_sync() increments the runtime PM usage counter
 *              even on failure. Error paths that return without calling
 *              pm_runtime_put() (or a sibling decrementer) leak the runtime
 *              PM reference count.
 * @kind problem
 * @problem.severity warning
 * @id cpp/pm-runtime-get-sync-leak
 * @tags reliability
 *       correctness
 *       resource-leak
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph

/**
 * A call to pm_runtime_get_sync (or the closely-related _get / resume_and_get
 * siblings that also bump the usage counter on error).
 */
class PmRuntimeGetCall extends FunctionCall {
  PmRuntimeGetCall() {
    this.getTarget().getName() = "pm_runtime_get_sync" or
    this.getTarget().getName() = "pm_runtime_get" or
    this.getTarget().getName() = "__pm_runtime_resume"
  }
}

/**
 * A call that decrements the runtime PM usage counter (any of the put family).
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
      n = "__pm_runtime_put_autosuspend" or
      n = "pm_runtime_disable"
    )
  }
}

/**
 * Holds if `ret` is the immediate return-value destination of the
 * pm_runtime_get_sync call `getCall`.
 */
predicate retOfGet(PmRuntimeGetCall getCall, Variable ret) {
  exists(AssignExpr ae |
    ae.getRValue() = getCall and
    ae.getLValue() = ret.getAnAccess()
  )
  or
  exists(Initializer init |
    init.getExpr() = getCall and
    init.getDeclaration() = ret
  )
}

/**
 * Holds if `cond` tests that `ret` indicates an error (e.g. `ret < 0`).
 */
predicate isErrorTest(Expr cond, Variable ret) {
  exists(RelationalOperation rel |
    rel = cond and
    rel.getAnOperand() = ret.getAnAccess() and
    rel.getAnOperand().getValue().toInt() = 0 and
    (rel instanceof LTExpr or rel instanceof LEExpr)
  )
  or
  exists(NEExpr ne |
    ne = cond and
    ne.getAnOperand() = ret.getAnAccess() and
    ne.getAnOperand().getValue().toInt() = 0
  )
}

/**
 * Holds if the basic block `bb` (or a transitively reachable successor on a
 * non-back-edge path) contains a PmRuntimePutCall reachable from `start`
 * without going through a function-return first.
 */
predicate reachesPut(ControlFlowNode start) {
  exists(PmRuntimePutCall put | start.getASuccessor*() = put)
}

from PmRuntimeGetCall getCall, Variable ret, IfStmt ifs, ReturnStmt rs
where
  retOfGet(getCall, ret) and
  ifs.getEnclosingFunction() = getCall.getEnclosingFunction() and
  isErrorTest(ifs.getCondition(), ret) and
  // the if-then directly returns ret (or any expr) without a put
  rs.getParent*() = ifs.getThen() and
  not exists(PmRuntimePutCall put |
    put.getEnclosingFunction() = getCall.getEnclosingFunction() and
    put.getParent*() = ifs.getThen()
  ) and
  // the get must dominate the if (rough check: get is before if in source)
  getCall.getLocation().getStartLine() < ifs.getLocation().getStartLine() and
  getCall.getEnclosingFunction() = ifs.getEnclosingFunction()
select getCall,
  "pm_runtime_get_sync (or sibling) bumps the PM usage counter even on failure; "
    + "the error branch at $@ returns without calling pm_runtime_put, leaking the refcount.",
  ifs, "this error path"
