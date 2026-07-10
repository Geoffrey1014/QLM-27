/**
 * @name  rq3-c2-lu-3-rep1
 * @id    cpp/rq3/c2/lu-3-rep1
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects pm_runtime_get_sync calls whose error-handling path
 *              returns without invoking pm_runtime_put, leaking the runtime
 *              PM usage count.
 */
import cpp

predicate isTargetCall(FunctionCall fc) {
  fc.getTarget().getName() = "pm_runtime_get_sync"
}

predicate isPutCall(FunctionCall fc, Expr devArg) {
  fc.getTarget().getName() in [
    "pm_runtime_put", "pm_runtime_put_noidle", "pm_runtime_put_sync",
    "pm_runtime_put_autosuspend", "pm_runtime_put_sync_autosuspend"
  ] and
  devArg = fc.getArgument(0)
}

predicate errorCheckOnTarget(FunctionCall tc, IfStmt ifs) {
  isTargetCall(tc) and
  exists(Variable v |
    (
      exists(AssignExpr a | a.getRValue() = tc and a.getLValue() = v.getAnAccess())
      or
      v.getInitializer().getExpr() = tc
    ) and
    ifs.getCondition().getAChild*() = v.getAnAccess()
  ) and
  ifs.getEnclosingFunction() = tc.getEnclosingFunction()
}

predicate errorBlockMissingPut(FunctionCall tc, IfStmt ifs) {
  errorCheckOnTarget(tc, ifs) and
  exists(Stmt thenStmt | thenStmt = ifs.getThen() |
    (
      thenStmt instanceof ReturnStmt
      or
      exists(ReturnStmt r | r.getParent*() = thenStmt)
      or
      exists(GotoStmt g | g.getParent*() = thenStmt)
    ) and
    not exists(FunctionCall pc, Expr devArg |
      isPutCall(pc, devArg) and
      pc.getParent*() = thenStmt and
      devArg.(VariableAccess).getTarget() = tc.getArgument(0).(VariableAccess).getTarget()
    )
  )
}

from FunctionCall tc, IfStmt ifs
where isTargetCall(tc) and errorCheckOnTarget(tc, ifs) and errorBlockMissingPut(tc, ifs)
select tc, "pm_runtime_get_sync return value checked but pm_runtime_put not called on error path — reference count leak."
