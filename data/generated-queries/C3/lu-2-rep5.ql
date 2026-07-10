/**
 * @name Memory leak via early return after acquire (C3 / lu-2)
 * @description Detects a call to an allocation API whose result is stored in a
 *              variable that is not released on every early-return path within
 *              the enclosing function. Mirrors the af9005_identify_state
 *              pattern (kmalloc -> ... -> return -EIO before kfree).
 * @kind problem
 * @problem.severity warning
 * @id qlm/c3-lu-2-rep5
 */

import cpp

predicate isAcquire(FunctionCall fc) {
  fc.getTarget().getName() in ["kmalloc", "kzalloc", "kcalloc", "kmalloc_array"]
}

predicate isRelease(FunctionCall fc, Expr arg) {
  fc.getTarget().getName() = "kfree" and arg = fc.getArgument(0)
}

Variable getAcquired(FunctionCall acq) {
  exists(AssignExpr ae | ae.getRValue() = acq and result.getAnAccess() = ae.getLValue())
  or
  exists(Initializer init | init.getExpr() = acq and result = init.getDeclaration())
}

predicate hasEarlyReturnLeak(FunctionCall acq, Variable v, ReturnStmt rs) {
  isAcquire(acq) and
  v = getAcquired(acq) and
  rs.getEnclosingFunction() = acq.getEnclosingFunction() and
  acq.getLocation().getStartLine() < rs.getLocation().getStartLine() and
  not exists(FunctionCall rel, Expr arg |
    isRelease(rel, arg) and
    arg = v.getAnAccess() and
    rel.getEnclosingFunction() = rs.getEnclosingFunction() and
    rel.getLocation().getStartLine() < rs.getLocation().getStartLine() and
    rel.getLocation().getStartLine() > acq.getLocation().getStartLine()
  ) and
  not exists(GotoStmt g |
    g.getEnclosingFunction() = rs.getEnclosingFunction() and
    g.getLocation().getStartLine() = rs.getLocation().getStartLine()
  )
}

from FunctionCall acq, Variable v, ReturnStmt rs
where hasEarlyReturnLeak(acq, v, rs)
select rs,
  "Potential memory leak: '" + v.getName() + "' allocated at line " +
    acq.getLocation().getStartLine() + " is not released before this return"
