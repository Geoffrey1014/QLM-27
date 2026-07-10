/**
 * @name Refcount leak: of_parse_phandle without of_node_put on early return
 * @description Detects functions where a device_node acquired via of_parse_phandle
 *              is not released with of_node_put before an early return path.
 * @kind problem
 * @problem.severity warning
 * @id cpp/qlm/l0/lin-3-rep1-of-node-refcount-leak
 */

import cpp

predicate hasReturnBeforeRelease(FunctionCall acq, Variable v) {
  acq.getTarget().getName() = "of_parse_phandle" and
  exists(AssignExpr a | a.getRValue() = acq and a.getLValue() = v.getAnAccess()) and
  exists(ReturnStmt ret, Function f |
    f = acq.getEnclosingFunction() and
    ret.getEnclosingFunction() = f and
    ret.getLocation().getStartLine() > acq.getLocation().getStartLine() and
    not exists(FunctionCall rel |
      rel.getTarget().getName() = "of_node_put" and
      rel.getEnclosingFunction() = f and
      rel.getArgument(0) = v.getAnAccess() and
      rel.getLocation().getStartLine() < ret.getLocation().getStartLine() and
      rel.getLocation().getStartLine() > acq.getLocation().getStartLine()
    )
  )
}

from FunctionCall acq, Variable v
where hasReturnBeforeRelease(acq, v)
select acq,
  "Refcount leak: " + v.getName() + " acquired by " + acq.getTarget().getName() +
    " may not be released on early return path."
