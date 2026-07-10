/**
 * @name Refcount leak: of_parse_phandle without matching of_node_put on all return paths
 * @description Detects the four-features (Lin) refcount-leak pattern where
 *              of_parse_phandle returns a node with incremented refcount but
 *              an early-return path skips the corresponding of_node_put.
 * @kind problem
 * @problem.severity warning
 * @id qlm/of-node-put-refcount-leak
 */

import cpp

predicate isAcquire(FunctionCall fc) {
  fc.getTarget().getName() = "of_parse_phandle"
}

predicate isRelease(FunctionCall fc, Expr arg) {
  fc.getTarget().getName() = "of_node_put" and
  arg = fc.getArgument(0)
}

Variable getAcquiredVar(FunctionCall fc) {
  isAcquire(fc) and
  exists(Assignment a |
    a.getRValue() = fc and result.getAnAccess() = a.getLValue())
}

predicate hasReleaseOnVar(Variable v, Function fn) {
  exists(FunctionCall rc, Expr a |
    isRelease(rc, a) and
    rc.getEnclosingFunction() = fn and
    a = v.getAnAccess())
}

predicate hasEarlyReturnBeforeRelease(FunctionCall acq, Variable v) {
  v = getAcquiredVar(acq) and
  exists(ReturnStmt r, Function fn |
    fn = acq.getEnclosingFunction() and
    r.getEnclosingFunction() = fn and
    r.getLocation().getStartLine() > acq.getLocation().getStartLine() and
    not exists(FunctionCall rc, Expr a |
      isRelease(rc, a) and
      rc.getEnclosingFunction() = fn and
      a = v.getAnAccess() and
      rc.getLocation().getStartLine() < r.getLocation().getStartLine() and
      rc.getLocation().getStartLine() > acq.getLocation().getStartLine()))
}

from FunctionCall acq, Variable v
where
  isAcquire(acq) and
  v = getAcquiredVar(acq) and
  hasEarlyReturnBeforeRelease(acq, v)
select acq,
  "Possible refcount leak: " + v.getName() + " from " + acq.getTarget().getName() +
    " may not have matching of_node_put on all return paths"
