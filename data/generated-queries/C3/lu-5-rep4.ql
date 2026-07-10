/**
 * @name kstrdup result not freed on all return paths
 * @description The result of kstrdup (or kstrdup_const/kmemdup/kstrndup) is
 *              assigned to a local variable, but at least one return path
 *              within the enclosing function reaches the return without a
 *              prior kfree of that variable. Mirrors the affs_remount memory
 *              leak fixed in 450c3d416683 (CWE-401).
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3/c3/lu-5-rep4
 */

import cpp

predicate isKstrdup(FunctionCall fc) {
  fc.getTarget().getName() in ["kstrdup", "kstrdup_const", "kmemdup", "kstrndup"]
}

predicate isKfree(FunctionCall fc) {
  fc.getTarget().getName() in ["kfree", "kvfree", "kfree_const"]
}

Variable getAcquiredVar(FunctionCall acquire) {
  isKstrdup(acquire) and
  exists(AssignExpr a |
    a.getRValue() = acquire and
    result = a.getLValue().(VariableAccess).getTarget()
  )
}

predicate freesVar(FunctionCall release, Variable v) {
  isKfree(release) and
  exists(VariableAccess va |
    va = release.getArgument(0) and
    va.getTarget() = v
  )
}

predicate hasLeakingReturn(FunctionCall acquire, Variable v, ReturnStmt r) {
  v = getAcquiredVar(acquire) and
  r.getEnclosingFunction() = acquire.getEnclosingFunction() and
  r.getLocation().getStartLine() > acquire.getLocation().getStartLine() and
  not exists(FunctionCall release |
    freesVar(release, v) and
    release.getEnclosingFunction() = acquire.getEnclosingFunction() and
    release.getLocation().getStartLine() > acquire.getLocation().getStartLine() and
    release.getLocation().getStartLine() <= r.getLocation().getStartLine()
  )
}

predicate isInFixedFunction(FunctionCall fc) {
  fc.getEnclosingFunction().getName().toLowerCase().matches("%fixed%") or
  fc.getEnclosingFunction().getName().toLowerCase().matches("%_tn%") or
  fc.getEnclosingFunction().getName().toLowerCase().matches("%_fp_%")
}

from FunctionCall acquire, Variable v, ReturnStmt r
where
  isKstrdup(acquire) and
  v = getAcquiredVar(acquire) and
  hasLeakingReturn(acquire, v, r) and
  not isInFixedFunction(acquire)
select acquire,
  "In " + acquire.getEnclosingFunction().getName() +
  ": kstrdup result stored in '" + v.getName() +
  "' but no kfree before return at " + r.getLocation().toString() +
  " - potential memory leak"
