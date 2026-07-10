/**
 * @name  rq3-c2-lu-3-rep2
 * @id    cpp/rq3/c2/lu-3-rep2
 * @kind  problem
 * @problem.severity warning
 * @description Detect missing pm_runtime_put on pm_runtime_get_sync error path (refcount leak).
 */

import cpp

predicate isTargetCall(FunctionCall fc) {
  fc.getTarget().getName() = "pm_runtime_get_sync"
}

predicate isPostOp(FunctionCall fc) {
  fc.getTarget().getName() = "pm_runtime_put" or
  fc.getTarget().getName() = "pm_runtime_put_noidle" or
  fc.getTarget().getName() = "pm_runtime_put_sync"
}

predicate errorCheckOnCall(IfStmt ifs, FunctionCall fc) {
  isTargetCall(fc) and
  exists(RelationalOperation rel |
    rel = ifs.getCondition().getAChild*() and
    rel.getAnOperand().getAChild*() = fc
    or
    rel = ifs.getCondition() and
    rel.getAnOperand() = fc
  )
  or
  isTargetCall(fc) and
  exists(Variable v, VariableAccess va |
    va = ifs.getCondition().getAChild*() and
    va.getTarget() = v and
    exists(AssignExpr ae |
      ae.getLValue().(VariableAccess).getTarget() = v and
      ae.getRValue() = fc
    )
  )
}

predicate errorBlockMissingPut(IfStmt ifs, FunctionCall fc) {
  errorCheckOnCall(ifs, fc) and
  exists(Stmt body | body = ifs.getThen() |
    body.getAChild*() instanceof ReturnStmt and
    not exists(FunctionCall pf |
      pf.getEnclosingStmt().getParentStmt*() = body and
      isPostOp(pf)
    )
  )
}

from IfStmt ifs, FunctionCall fc
where errorBlockMissingPut(ifs, fc)
select fc, "pm_runtime_get_sync error path may leak refcount: missing pm_runtime_put."
