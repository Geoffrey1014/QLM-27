/**
 * @name Missing of_node_put on early-return path after device-tree acquisition
 * @description An of_*-family call returns a struct device_node* whose
 *              refcount has been incremented. When a subsequent IS_ERR()-
 *              style early return is placed BEFORE the of_node_put()
 *              call, the error path leaks the device-tree node reference
 *              (CWE-401). The fix is to move of_node_put() above the
 *              early-return guard.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-lin-3
 */

import cpp

/* APIs that acquire a struct device_node* whose refcount must be released. */
predicate isOfAcquireApi(string name) {
  name = "of_parse_phandle" or
  name = "of_parse_phandle_with_args" or
  name = "of_find_node_by_name" or
  name = "of_find_node_by_path" or
  name = "of_find_node_opts_by_path" or
  name = "of_find_node_by_phandle" or
  name = "of_find_matching_node" or
  name = "of_find_matching_node_and_match" or
  name = "of_find_compatible_node" or
  name = "of_get_child_by_name" or
  name = "of_get_next_child" or
  name = "of_get_next_available_child" or
  name = "of_get_parent" or
  name = "of_get_next_parent" or
  name = "of_get_cpu_node" or
  name = "of_irq_find_parent"
}

predicate isOfReleaseCall(FunctionCall c) {
  c.getTarget().getName() = "of_node_put"
}

/* The Variable that receives `call`'s return value, either via initialization
 * (`T *v = call(...)`) or assignment (`v = call(...)`). */
Variable getReceiverVariable(FunctionCall call) {
  exists(Variable v |
    v.getInitializer().getExpr() = call and result = v
  )
  or
  exists(AssignExpr a |
    a.getRValue() = call and
    result = a.getLValue().(VariableAccess).getTarget()
  )
}

/* of_node_put(v) call inside function f targeting variable v. */
predicate releaseOf(Function f, Variable v, FunctionCall put) {
  isOfReleaseCall(put) and
  put.getEnclosingFunction() = f and
  put.getArgument(0).(VariableAccess).getTarget() = v
}

/* A return statement located textually between the acquire call and the
 * (first) release-on-v in the same function -- i.e. an early exit on
 * which the put never executes. */
predicate hasUnguardedEarlyReturn(
  FunctionCall acquire, Variable v, ReturnStmt ret
) {
  exists(Function f, Location aLoc, Location rLoc |
    f = acquire.getEnclosingFunction() and
    ret.getEnclosingFunction() = f and
    aLoc = acquire.getLocation() and
    rLoc = ret.getLocation() and
    aLoc.getFile() = rLoc.getFile() and
    /* return appears AFTER the acquire ... */
    rLoc.getStartLine() > aLoc.getStartLine() and
    /* ... and BEFORE every release-on-v in the same function (or there
     * is no release on v at all). */
    forall(FunctionCall put |
      releaseOf(f, v, put) |
      rLoc.getStartLine() < put.getLocation().getStartLine()
    ) and
    /* ensure at least one release exists for v in f (the bug pattern is
     * "release exists but is unreachable on this path"); without a release
     * at all the simpler missing-of_node_put detector applies, but we also
     * cover that case to keep recall up. */
    (
      exists(FunctionCall put | releaseOf(f, v, put))
      or
      not exists(FunctionCall put | releaseOf(f, v, put))
    )
  )
}

from FunctionCall acquire, Variable v, ReturnStmt ret
where
  isOfAcquireApi(acquire.getTarget().getName()) and
  v = getReceiverVariable(acquire) and
  hasUnguardedEarlyReturn(acquire, v, ret)
select acquire,
  "Call to " + acquire.getTarget().getName() +
    " stores a refcounted device_node in '" + v.getName() +
    "'; an early return at line " + ret.getLocation().getStartLine() +
    " bypasses the of_node_put() release -- reference leak on the error path."
