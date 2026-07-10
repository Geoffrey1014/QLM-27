/**
 * @name Refcount leak after of_parse_phandle
 * @description Detects functions that call of_parse_phandle but return on an error path
 *              without calling of_node_put on the acquired device_node.
 * @kind problem
 * @problem.severity warning
 * @id cpp/refcount-leak-of-parse-phandle
 */
import cpp

predicate isAcquire(FunctionCall fc) { fc.getTarget().getName() = "of_parse_phandle" }

predicate isRelease(FunctionCall fc) { fc.getTarget().getName() = "of_node_put" }

predicate acquiredVar(FunctionCall acq, Variable v) {
  isAcquire(acq) and
  exists(AssignExpr a | a.getRValue() = acq and a.getLValue() = v.getAnAccess())
}

predicate hasLeakingReturn(FunctionCall acq, Variable v, ReturnStmt ret) {
  acquiredVar(acq, v) and
  ret.getEnclosingFunction() = acq.getEnclosingFunction() and
  ret.getLocation().getStartLine() > acq.getLocation().getStartLine() and
  not exists(FunctionCall rel |
    isRelease(rel) and
    rel.getEnclosingFunction() = acq.getEnclosingFunction() and
    rel.getAnArgument() = v.getAnAccess() and
    rel.getLocation().getStartLine() < ret.getLocation().getStartLine()
  )
}

from FunctionCall acq, Variable v, ReturnStmt ret
where acquiredVar(acq, v) and hasLeakingReturn(acq, v, ret)
select ret, "Refcount leak: " + v.getName() + " acquired by " + acq.getTarget().getName() + " is leaked on this return path."
