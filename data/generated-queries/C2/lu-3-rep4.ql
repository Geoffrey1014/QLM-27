/**
 * @name  rq3-c2-lu-3-rep4
 * @id    cpp/rq3/c2/lu-3-rep4
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects pm_runtime_get_sync() error paths that return without
 *              calling pm_runtime_put(), causing a reference count leak.
 */

import cpp

/** A call to pm_runtime_get_sync. */
predicate isTargetCall(FunctionCall fc) {
  fc.getTarget().getName() = "pm_runtime_get_sync"
}

/** A call to pm_runtime_put (or _noidle/_sync), the resource release. */
predicate isCleanupCall(FunctionCall fc) {
  fc.getTarget().getName() = "pm_runtime_put" or
  fc.getTarget().getName() = "pm_runtime_put_noidle" or
  fc.getTarget().getName() = "pm_runtime_put_sync"
}

/**
 * `ifs` is an if-statement whose condition tests the result of `tcall`
 * (a pm_runtime_get_sync call) for failure (typically `ret < 0`).
 * We approximate by: ifs is in the same function as tcall, the tcall's
 * enclosing variable assignment flows into the condition, and the condition
 * mentions a comparison `< 0`.
 */
predicate isFailureGuard(IfStmt ifs, FunctionCall tcall) {
  isTargetCall(tcall) and
  ifs.getEnclosingFunction() = tcall.getEnclosingFunction() and
  exists(Variable v, VariableAccess va, RelationalOperation cmp |
    // tcall's value is assigned to v
    exists(Expr asn |
      asn.(AssignExpr).getLValue().(VariableAccess).getTarget() = v and
      asn.(AssignExpr).getRValue() = tcall
      or
      v.getInitializer().getExpr() = tcall
    ) and
    cmp = ifs.getCondition().getAChild*() and
    va = cmp.getAnOperand() and
    va.getTarget() = v and
    cmp.getOperator() = "<"
  ) and
  // tcall must lexically precede the if
  tcall.getLocation().getStartLine() < ifs.getLocation().getStartLine()
}

/**
 * The "then" branch of `ifs` contains a cleanup call (pm_runtime_put*).
 */
predicate branchHasCleanup(IfStmt ifs) {
  exists(FunctionCall cc |
    isCleanupCall(cc) and
    cc.getEnclosingStmt().getParentStmt*() = ifs.getThen()
  )
}

/**
 * The "then" branch of `ifs` contains a ReturnStmt (early return on failure).
 */
predicate branchReturns(IfStmt ifs) {
  exists(ReturnStmt rs |
    rs.getParentStmt*() = ifs.getThen()
  )
}

/**
 * Composite: failure-guarded pm_runtime_get_sync where the failure branch
 * returns without calling pm_runtime_put -> reference count leak.
 */
predicate missingCleanupOnFailure(FunctionCall tcall, IfStmt ifs) {
  isTargetCall(tcall) and
  isFailureGuard(ifs, tcall) and
  branchReturns(ifs) and
  not branchHasCleanup(ifs)
}

from FunctionCall tcall, IfStmt ifs
where missingCleanupOnFailure(tcall, ifs)
select tcall,
  "pm_runtime_get_sync() failure path at $@ returns without calling pm_runtime_put(), causing a refcount leak.",
  ifs, "this if-statement"
