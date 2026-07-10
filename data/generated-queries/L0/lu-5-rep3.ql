/**
 * @name L0 generated query for lu-5 / fix 450c3d416683
 * @description Missing kfree(new_opts) after kstrdup in affs_remount — memory leak (CWE-401)
 * @kind problem
 * @problem.severity warning
 * @id cpp/rq3/l0/lu-5-rep3
 */

import cpp

predicate hasMissingKfreeAfterKstrdup(FunctionCall acquire, Variable v) {
  acquire.getTarget().getName() = "kstrdup" and
  exists(AssignExpr assign |
    assign.getRValue() = acquire and
    v = assign.getLValue().(VariableAccess).getTarget()
  ) and
  v.getType().getUnspecifiedType() instanceof PointerType and
  exists(ReturnStmt ret |
    ret.getEnclosingFunction() = acquire.getEnclosingFunction() and
    not exists(FunctionCall rel |
      rel.getEnclosingFunction() = acquire.getEnclosingFunction() and
      rel.getTarget().getName() = "kfree" and
      exists(VariableAccess va |
        va = rel.getArgument(0) and va.getTarget() = v
      ) and
      rel.getLocation().getStartLine() < ret.getLocation().getStartLine()
    )
  ) and
  not acquire.getEnclosingFunction().getName().toLowerCase().matches("%fixed%")
}

from FunctionCall acquire, Variable v
where hasMissingKfreeAfterKstrdup(acquire, v)
select acquire,
  "Missing kfree() for variable '" + v.getName() +
  "' allocated by " + acquire.getTarget().getName() +
  "() — potential memory leak"
