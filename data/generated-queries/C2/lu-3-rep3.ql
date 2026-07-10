/**
 * @name  rq3-c2-lu-3-rep3
 * @id    cpp/rq3/c2/lu-3-rep3
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects missing pm_runtime_put on the error path of pm_runtime_get_sync.
 */
import cpp

predicate isTargetCall(FunctionCall fc) {
  fc.getTarget().getName() = "pm_runtime_get_sync"
}

predicate errorCheckOnTarget(FunctionCall fc, IfStmt ifs) {
  exists(Expr cond | cond = ifs.getCondition() |
    // Direct: if (pm_runtime_get_sync(...) < 0)
    exists(RelationalOperation rel |
      cond = rel and
      rel.getAnOperand() = fc
    )
    or
    // Indirect via a variable: ret = pm_runtime_get_sync(...); if (ret < 0)
    exists(Variable v, AssignExpr ae |
      ae.getRValue() = fc and
      ae.getLValue() = v.getAnAccess() and
      cond.(RelationalOperation).getAnOperand() = v.getAnAccess() and
      // ordering: assignment dominates the if
      ae.getEnclosingFunction() = ifs.getEnclosingFunction()
    )
  )
}

predicate errorBranchReturns(IfStmt ifs) {
  exists(Stmt thn | thn = ifs.getThen() |
    thn instanceof ReturnStmt
    or
    thn.(BlockStmt).getAStmt() instanceof ReturnStmt
  )
}

predicate missingRelease(IfStmt ifs, FunctionCall fc) {
  isTargetCall(fc) and
  errorCheckOnTarget(fc, ifs) and
  not exists(FunctionCall release |
    release.getTarget().getName() = "pm_runtime_put" and
    release.getEnclosingFunction() = ifs.getEnclosingFunction() and
    (
      release.getEnclosingStmt().getParent*() = ifs.getThen()
      or
      release.getEnclosingStmt() = ifs.getThen()
    )
  )
}

from FunctionCall fc, IfStmt ifs
where
  isTargetCall(fc) and
  errorCheckOnTarget(fc, ifs) and
  errorBranchReturns(ifs) and
  missingRelease(ifs, fc)
select fc, "pm_runtime_get_sync error path may leak runtime PM reference: missing pm_runtime_put on failure."
