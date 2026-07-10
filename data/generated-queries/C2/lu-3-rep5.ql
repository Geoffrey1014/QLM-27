/**
 * @name  rq3-c2-lu-3-rep5
 * @id    cpp/rq3/c2/lu-3-rep5
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2. Detect missing
 *              pm_runtime_put on pm_runtime_get_sync error path (refcount leak).
 */

import cpp

predicate is_target_call(FunctionCall fc) {
  fc.getTarget().getName() = "pm_runtime_get_sync"
}

predicate is_release_call(FunctionCall fc, Expr dev) {
  (fc.getTarget().getName() = "pm_runtime_put" or
   fc.getTarget().getName() = "pm_runtime_put_sync" or
   fc.getTarget().getName() = "pm_runtime_put_noidle" or
   fc.getTarget().getName() = "pm_runtime_put_autosuspend") and
  dev = fc.getArgument(0)
}

predicate on_error_branch(FunctionCall tc, IfStmt ifs) {
  is_target_call(tc) and
  (
    // if (pm_runtime_get_sync(...) < 0) { ... }
    exists(Expr cond | cond = ifs.getCondition() |
      cond.getAChild*() = tc
    )
    or
    // ret = pm_runtime_get_sync(...); if (ret < 0) { ... }
    exists(Variable v, AssignExpr ae, VariableAccess va |
      ae.getRValue() = tc and
      ae.getLValue() = v.getAnAccess() and
      va = ifs.getCondition().getAChild*() and
      va.getTarget() = v
    )
    or
    // int ret = pm_runtime_get_sync(...); if (ret < 0)
    exists(Variable v, VariableAccess va |
      v.getInitializer().getExpr() = tc and
      va = ifs.getCondition().getAChild*() and
      va.getTarget() = v
    )
  )
}

predicate release_reachable_on_error(FunctionCall tc, IfStmt ifs) {
  on_error_branch(tc, ifs) and
  exists(FunctionCall rel, Expr dev |
    is_release_call(rel, dev) and
    rel.getEnclosingStmt().getParentStmt*() = ifs.getThen()
  )
}

predicate missing_release_on_error(FunctionCall tc) {
  exists(IfStmt ifs |
    on_error_branch(tc, ifs) and
    // the then-branch returns / exits without calling release
    exists(ReturnStmt rs | rs.getParentStmt*() = ifs.getThen()) and
    not release_reachable_on_error(tc, ifs)
  )
}

from FunctionCall tc
where missing_release_on_error(tc)
select tc,
  "pm_runtime_get_sync may leak a runtime PM reference on the error path; missing pm_runtime_put."
