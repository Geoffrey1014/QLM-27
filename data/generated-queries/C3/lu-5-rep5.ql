/**
 * @name C3 generated query for lu-5 / fix 450c3d416683
 * @description Missing kfree after kstrdup — memory leak in affs_remount (CWE-401)
 * @kind problem
 * @problem.severity warning
 * @id cpp/rq3/c3/lu-5-rep5
 */

import cpp

predicate isAcquisition(FunctionCall fc) {
  fc.getTarget().getName() = "kstrdup"
}

predicate isReleaseCall(FunctionCall fc) {
  fc.getTarget().getName() = "kfree"
}

Variable getAcquiredVariable(FunctionCall acquire) {
  exists(AssignExpr a |
    a.getRValue() = acquire and
    result = a.getLValue().(VariableAccess).getTarget()
  )
}

predicate hasNullCheck(FunctionCall acquire, Variable v) {
  exists(IfStmt ifStmt, VariableAccess va |
    ifStmt.getEnclosingFunction() = acquire.getEnclosingFunction() and
    va.getTarget() = v and
    ifStmt.getCondition().getAChild*() = va
  )
}

predicate isInFixedFunction(FunctionCall fc) {
  fc.getEnclosingFunction().getName().toLowerCase().matches("%fixed%")
}

/* Leak detector: a return statement exists after the acquire such that no
 * release of the acquired variable precedes it (within the same function,
 * post-acquire region). */
predicate hasUnreleasedReturn(FunctionCall acquire, Variable v) {
  exists(ReturnStmt rs |
    rs.getEnclosingFunction() = acquire.getEnclosingFunction() and
    rs.getLocation().getStartLine() > acquire.getLocation().getStartLine() and
    not exists(FunctionCall rel, VariableAccess va |
      isReleaseCall(rel) and
      rel.getEnclosingFunction() = acquire.getEnclosingFunction() and
      va = rel.getArgument(0) and
      va.getTarget() = v and
      rel.getLocation().getStartLine() > acquire.getLocation().getStartLine() and
      rel.getLocation().getStartLine() < rs.getLocation().getStartLine()
    )
  )
}

from FunctionCall acquire, Variable acquiredVar
where
  isAcquisition(acquire) and
  acquiredVar = getAcquiredVariable(acquire) and
  hasNullCheck(acquire, acquiredVar) and
  hasUnreleasedReturn(acquire, acquiredVar) and
  not isInFixedFunction(acquire)
select acquire,
  "Call to " + acquire.getTarget().getName() +
    " stores result in '" + acquiredVar.getName() +
    "' but kfree() is missing on at least one return path, causing a memory leak"
