/**
 * @name Missing of_node_put on an error-return path after device-tree
 *       node acquisition
 * @description An of_*-family routine returns a struct device_node*
 *              with its refcount incremented; the caller must release
 *              the reference via of_node_put() on every error-return
 *              path. When the count of of_node_put() releases on the
 *              acquired variable is strictly less than the number of
 *              return statements reachable from the acquisition, at
 *              least one path leaks the reference (CWE-401).
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-lin-4
 */

import cpp

/**
 * Linux of_* helpers that return a refcounted struct device_node*.
 * The caller must drop the reference via of_node_put() on every path.
 */
predicate ofNodeAcquireName(string n) {
  n = "of_parse_phandle" or
  n = "of_find_node_by_name" or
  n = "of_find_node_by_path" or
  n = "of_find_node_opts_by_path" or
  n = "of_find_matching_node" or
  n = "of_find_matching_node_and_match" or
  n = "of_find_compatible_node" or
  n = "of_get_child_by_name" or
  n = "of_get_next_child" or
  n = "of_get_next_available_child" or
  n = "of_get_parent" or
  n = "of_get_next_parent" or
  n = "of_get_cpu_node" or
  n = "of_irq_find_parent"
}

/** Variable that receives the result of `acq` (via init or assignment). */
Variable acquiredInto(FunctionCall acq) {
  exists(Variable v |
    v.getInitializer().getExpr() = acq and result = v
  )
  or
  exists(AssignExpr a |
    a.getRValue() = acq and
    result = a.getLValue().(VariableAccess).getTarget()
  )
}

/**
 * Number of of_node_put() calls inside `f` whose first argument is a
 * read of `v`.
 */
int releaseCountOn(Function f, Variable v) {
  result = count(FunctionCall put |
                   put.getTarget().getName() = "of_node_put" and
                   put.getEnclosingFunction() = f and
                   put.getArgument(0).(VariableAccess).getTarget() = v)
}

/**
 * Number of return statements in `f` that lie textually after `acq`
 * AND are NOT guarded by an immediate "if (!recv) return ..." NULL
 * check on the acquired pointer (which is the well-known "acquire
 * failed" early-out and does not leak anything).
 */
int returnsAfter(Function f, FunctionCall acq, Variable recv) {
  result = count(ReturnStmt r |
                   r.getEnclosingFunction() = f and
                   r.getLocation().getStartLine() > acq.getLocation().getStartLine() and
                   not exists(IfStmt guard, NotExpr ne, VariableAccess va |
                     guard.getEnclosingFunction() = f and
                     ne = guard.getCondition() and
                     va = ne.getOperand() and
                     va.getTarget() = recv and
                     (guard.getThen() = r or
                      r.getParent*() = guard.getThen())
                   ))
}

from FunctionCall acq, Variable recv, Function f, int releases, int rets
where
  ofNodeAcquireName(acq.getTarget().getName()) and
  recv = acquiredInto(acq) and
  f = acq.getEnclosingFunction() and
  releases = releaseCountOn(f, recv) and
  rets = returnsAfter(f, acq, recv) and
  // At least one error-return path is not balanced by a release.
  rets > releases
select acq,
  "of_node_put() on '" + recv.getName() + "' is missing on at least one " +
    "return path after " + acq.getTarget().getName() +
    " (releases=" + releases + ", returns-after-acquire=" + rets + "): refcount leak."
