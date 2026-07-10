/**
 * @name Memory leak via early-return bypassing kfree
 * @description Detects functions that allocate memory with kmalloc/kzalloc/kcalloc
 *              and later release it with kfree, but contain at least one
 *              `return` statement reached after the allocation that does not
 *              return the acquired pointer and is not preceded by the release.
 *              Pattern: af9005_identify_state memleak (commit 2289adbfa559).
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3-c3-lu2-rep2-memleak-kmalloc
 */

import cpp

predicate isAcquire(FunctionCall fc) {
  fc.getTarget().getName() = "kmalloc" or
  fc.getTarget().getName() = "kzalloc" or
  fc.getTarget().getName() = "kcalloc"
}

Variable getAcquired(FunctionCall fc) {
  isAcquire(fc) and
  exists(AssignExpr ae | ae.getRValue() = fc and ae.getLValue() = result.getAnAccess())
}

predicate hasReleaseInFunction(Function f, Variable v) {
  exists(FunctionCall rc |
    rc.getEnclosingFunction() = f and
    rc.getTarget().getName() = "kfree" and
    rc.getAnArgument() = v.getAnAccess())
}

predicate earlyReturnBypassingRelease(FunctionCall acq, Variable v, ReturnStmt rs) {
  v = getAcquired(acq) and
  rs.getEnclosingFunction() = acq.getEnclosingFunction() and
  hasReleaseInFunction(acq.getEnclosingFunction(), v) and
  rs.getLocation().getStartLine() > acq.getLocation().getStartLine() and
  not exists(FunctionCall rc |
    rc.getEnclosingFunction() = acq.getEnclosingFunction() and
    rc.getTarget().getName() = "kfree" and
    rc.getAnArgument() = v.getAnAccess() and
    rc.getLocation().getStartLine() < rs.getLocation().getStartLine()) and
  not rs.getExpr().(VariableAccess).getTarget() = v
}

from FunctionCall acq, Variable v, ReturnStmt rs
where earlyReturnBypassingRelease(acq, v, rs)
select rs, "Potential memory leak: " + v.getName() + " allocated at line " +
           acq.getLocation().getStartLine().toString() +
           " is not released before this return."
