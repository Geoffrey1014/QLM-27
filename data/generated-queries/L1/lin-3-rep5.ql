/**
 * @name of_node_refcount_leak (four-features-Lin, L1)
 * @description Detects of_parse_phandle acquires whose returned node may not be released via of_node_put on an early return path.
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3-l1-lin-3-rep5
 */

import cpp

predicate isAcquire(FunctionCall fc) {
  fc.getTarget().getName() = "of_parse_phandle"
}

predicate leaksOnErrorPath(FunctionCall acq, Variable v) {
  isAcquire(acq) and
  exists(AssignExpr a | a.getRValue() = acq and a.getLValue() = v.getAnAccess()) and
  exists(ReturnStmt ret, Function f |
    f = acq.getEnclosingFunction() and
    ret.getEnclosingFunction() = f and
    ret.getLocation().getStartLine() > acq.getLocation().getStartLine() and
    not exists(FunctionCall rel |
      rel.getTarget().getName() = "of_node_put" and
      rel.getEnclosingFunction() = f and
      rel.getArgument(0) = v.getAnAccess() and
      rel.getLocation().getStartLine() > acq.getLocation().getStartLine() and
      rel.getLocation().getStartLine() < ret.getLocation().getStartLine()
    )
  )
}

from FunctionCall acq, Variable v
where leaksOnErrorPath(acq, v)
select acq,
  "Potential refcount leak: " + v.getName() + " acquired by " + acq.getTarget().getName() +
    " may not be released on early return."
