/**
 * @name kstrdup result not freed on all return paths
 * @description The result of kstrdup (or kstrdup_const/kmemdup/kstrndup) is
 *              assigned to a local variable, but at least one return path
 *              within the enclosing function reaches the return without a
 *              prior kfree of that variable. Mirrors the affs_remount memory
 *              leak fixed in 450c3d416683 (CWE-401).
 * @kind problem
 * @problem.severity warning
 * @id qlm/l0-lu5-kstrdup-leak
 * @tags reliability
 *       correctness
 *       resource-leak
 */

import cpp

predicate isKstrdup(FunctionCall fc) {
  fc.getTarget().getName() in ["kstrdup", "kstrdup_const", "kmemdup", "kstrndup"]
}

from FunctionCall acquire, Variable v, ReturnStmt r, Function enclosing
where
  isKstrdup(acquire) and
  enclosing = acquire.getEnclosingFunction() and
  exists(AssignExpr a |
    a.getRValue() = acquire and
    v = a.getLValue().(VariableAccess).getTarget()
  ) and
  r.getEnclosingFunction() = enclosing and
  r.getLocation().getStartLine() > acquire.getLocation().getStartLine() and
  not exists(FunctionCall release, VariableAccess va |
    release.getTarget().getName() in ["kfree", "kvfree", "kfree_const"] and
    release.getEnclosingFunction() = enclosing and
    va = release.getArgument(0) and
    va.getTarget() = v and
    release.getLocation().getStartLine() > acquire.getLocation().getStartLine() and
    release.getLocation().getStartLine() <= r.getLocation().getStartLine()
  ) and
  not enclosing.getName().toLowerCase().matches("%fixed%") and
  not enclosing.getName().toLowerCase().matches("%_tn%") and
  not enclosing.getName().toLowerCase().matches("%_fp_%")
select acquire,
  "kstrdup result stored in '" + v.getName() +
  "' but no kfree before return at " + r.getLocation().toString() +
  " in " + enclosing.getName() + " - potential memory leak"
