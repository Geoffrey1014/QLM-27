/**
 * @name Refcount leak: of_parse_phandle without of_node_put on error paths
 * @description Detects functions that acquire a device_node via
 *              of_parse_phandle but return on some path without calling
 *              of_node_put on the acquired variable.
 * @kind problem
 * @problem.severity warning
 * @id qlm/lin-4-rep4
 */

import cpp

predicate isAcquire(FunctionCall fc) {
  fc.getTarget().getName() = "of_parse_phandle"
}

predicate getAcquiredVar(FunctionCall fc, Variable v) {
  isAcquire(fc) and
  exists(AssignExpr a | a.getRValue() = fc and a.getLValue() = v.getAnAccess())
}

predicate isRelease(FunctionCall fc, Variable v) {
  fc.getTarget().getName() = "of_node_put" and
  fc.getArgument(0) = v.getAnAccess()
}

predicate leakyReturn(FunctionCall acq, Variable v, ReturnStmt ret) {
  getAcquiredVar(acq, v) and
  ret.getEnclosingFunction() = acq.getEnclosingFunction() and
  acq.getLocation().getStartLine() < ret.getLocation().getStartLine() and
  not exists(FunctionCall rel |
    isRelease(rel, v) and
    rel.getEnclosingFunction() = acq.getEnclosingFunction() and
    rel.getLocation().getStartLine() < ret.getLocation().getStartLine()
  )
}

from FunctionCall acq, Variable v, ReturnStmt ret
where leakyReturn(acq, v, ret)
select acq,
  "Refcount leak: $@ acquired via of_parse_phandle is not released before return at line " +
    ret.getLocation().getStartLine().toString(),
  v, v.getName()
