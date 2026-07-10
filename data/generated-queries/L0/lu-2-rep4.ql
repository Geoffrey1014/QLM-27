/**
 * @name Memory leak: kmalloc with early-return bypassing kfree
 * @description Detects kmalloc-family allocations whose enclosing function
 *              contains a ReturnStmt reachable from the allocation without
 *              an intervening kfree on the allocated variable.
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3-l0-lu2-rep4
 */
import cpp

predicate leaksOnEarlyReturn(FunctionCall acq, Variable v, ReturnStmt r) {
  acq.getTarget().getName() in ["kmalloc", "kzalloc", "kcalloc"] and
  exists(AssignExpr ae |
    ae.getRValue() = acq and
    ae.getLValue() = v.getAnAccess()
  ) and
  r.getEnclosingFunction() = acq.getEnclosingFunction() and
  acq.getASuccessor+() = r and
  not exists(FunctionCall rel |
    rel.getTarget().getName() = "kfree" and
    rel.getArgument(0) = v.getAnAccess() and
    acq.getASuccessor+() = rel and
    rel.getASuccessor+() = r
  )
}

from FunctionCall acq, Variable v, ReturnStmt r
where leaksOnEarlyReturn(acq, v, r)
select acq,
  "Possible memory leak: '" + v.getName() +
  "' allocated by " + acq.getTarget().getName() +
  "() may be leaked at return on line " + r.getLocation().getStartLine() + "."
