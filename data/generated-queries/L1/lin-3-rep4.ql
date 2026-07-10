/**
 * @name of_parse_phandle refcount leak on early-return path
 * @description Detects functions that acquire a device_node via
 *              of_parse_phandle() and take an early-return path
 *              without calling of_node_put() on the acquired node.
 * @kind problem
 * @problem.severity warning
 * @id qlm/lin3-rep4
 * @tags reliability
 */
import cpp

predicate isPhandleAcquireLeaked(FunctionCall acq, Variable v) {
  acq.getTarget().getName() = "of_parse_phandle" and
  v.getAnAssignedValue() = acq and
  exists(ReturnStmt ret, Function f |
    f = acq.getEnclosingFunction() and
    ret.getEnclosingFunction() = f and
    ret.getLocation().getStartLine() > acq.getLocation().getStartLine() and
    not exists(FunctionCall rel |
      rel.getTarget().getName() = "of_node_put" and
      rel.getEnclosingFunction() = f and
      rel.getAnArgument() = v.getAnAccess() and
      rel.getLocation().getStartLine() < ret.getLocation().getStartLine() and
      rel.getLocation().getStartLine() > acq.getLocation().getStartLine()
    )
  )
}

from FunctionCall acq, Variable v
where isPhandleAcquireLeaked(acq, v)
select acq,
  "Leaked of_parse_phandle refcount on variable " + v.getName() +
  " (missing of_node_put on early-return path)"
