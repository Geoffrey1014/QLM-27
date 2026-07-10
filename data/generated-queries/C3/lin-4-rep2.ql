/**
 * @name Refcount leak: of_parse_phandle without of_node_put on error path
 * @description Detects functions that acquire a device_node via of_parse_phandle
 *              and return on some path without calling of_node_put on it.
 * @kind problem
 * @problem.severity warning
 * @id qlm/of-parse-phandle-leak-lin4r2
 */

import cpp

predicate isAcquire(FunctionCall fc) {
  fc.getTarget().getName() = "of_parse_phandle"
}

predicate isRelease(FunctionCall fc, Expr arg) {
  fc.getTarget().getName() = "of_node_put" and arg = fc.getArgument(0)
}

predicate acquiredVariable(FunctionCall acq, LocalVariable v) {
  isAcquire(acq) and
  (
    exists(AssignExpr a |
      a.getLValue() = v.getAnAccess() and a.getRValue() = acq
    )
    or
    v.getInitializer().getExpr() = acq
  )
}

predicate releasesVarBetween(LocalVariable v, FunctionCall acq, ReturnStmt r) {
  exists(FunctionCall rel, Expr arg |
    isRelease(rel, arg) and
    arg = v.getAnAccess() and
    rel.getEnclosingFunction() = r.getEnclosingFunction() and
    rel.getLocation().getStartLine() > acq.getLocation().getStartLine() and
    rel.getLocation().getStartLine() < r.getLocation().getStartLine()
  )
}

predicate leakingReturn(ReturnStmt r, LocalVariable v, FunctionCall acq) {
  acquiredVariable(acq, v) and
  r.getEnclosingFunction() = acq.getEnclosingFunction() and
  r.getLocation().getStartLine() > acq.getLocation().getStartLine() and
  not releasesVarBetween(v, acq, r)
}

from FunctionCall acq, LocalVariable v, ReturnStmt r
where
  acquiredVariable(acq, v) and
  leakingReturn(r, v, acq)
select r,
  "refcount leak: $@ acquired via $@ not released before this return",
  v, v.getName(),
  acq, acq.getTarget().getName()
