/**
 * @name  rq3-c2-lin-4-rep4
 * @id    cpp/rq3/c2/lin-4-rep4
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects missing of_node_put on a node acquired via of_parse_phandle
 *              before an early return.
 */
import cpp

predicate acquiresNode(FunctionCall fc, Variable v) {
  fc.getTarget().getName() = "of_parse_phandle" and
  exists(AssignExpr ae |
    ae.getRValue() = fc and
    ae.getLValue() = v.getAnAccess())
}

predicate releasesNode(FunctionCall rc, Variable v) {
  rc.getTarget().getName() = "of_node_put" and
  rc.getArgument(0) = v.getAnAccess()
}

predicate returnAfterAcquire(ReturnStmt rs, FunctionCall acquire, Variable v) {
  acquiresNode(acquire, v) and
  rs.getEnclosingFunction() = acquire.getEnclosingFunction() and
  acquire.getLocation().getStartLine() < rs.getLocation().getStartLine()
}

predicate missingReleaseBeforeReturn(ReturnStmt rs, FunctionCall acquire, Variable v) {
  returnAfterAcquire(rs, acquire, v) and
  not exists(FunctionCall rc |
    releasesNode(rc, v) and
    rc.getEnclosingFunction() = rs.getEnclosingFunction() and
    rc.getLocation().getStartLine() >= acquire.getLocation().getStartLine() and
    rc.getLocation().getStartLine() <= rs.getLocation().getStartLine())
}

from ReturnStmt rs, FunctionCall acquire, Variable v
where missingReleaseBeforeReturn(rs, acquire, v)
select rs, "Possible refcount leak: '" + v.getName() + "' acquired by of_parse_phandle at $@ is not released by of_node_put before this return.", acquire, acquire.toString()
