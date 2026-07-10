/**
 * @name  rq3-c2-lin-3-rep5
 * @id    cpp/rq3/c2/lin-3-rep5
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects missing of_node_put() on a device_node returned by
 *              of_parse_phandle() along some path to a function return.
 */
import cpp

predicate is_acquire_call(FunctionCall fc, Variable v) {
  fc.getTarget().getName() = "of_parse_phandle" and
  exists(Assignment a |
    a.getRValue() = fc and
    a.getLValue() = v.getAnAccess())
}

predicate is_release_call_on(FunctionCall fc, Variable v) {
  fc.getTarget().getName() = "of_node_put" and
  fc.getArgument(0) = v.getAnAccess()
}

predicate release_reaches_exit_from(FunctionCall acquire, Variable v) {
  is_acquire_call(acquire, v) and
  exists(FunctionCall rel |
    is_release_call_on(rel, v) and
    rel.getEnclosingFunction() = acquire.getEnclosingFunction() and
    acquire.getASuccessor*() = rel)
}

predicate reachableAvoidingRelease(ControlFlowNode src, ControlFlowNode dst, Variable v) {
  src = dst
  or
  exists(ControlFlowNode mid |
    src.getASuccessor() = mid and
    not is_release_call_on(mid, v) and
    reachableAvoidingRelease(mid, dst, v))
}

predicate leaks_on_some_path(FunctionCall acquire, Variable v) {
  is_acquire_call(acquire, v) and
  exists(ReturnStmt ret |
    ret.getEnclosingFunction() = acquire.getEnclosingFunction() and
    reachableAvoidingRelease(acquire, ret, v))
}

from FunctionCall acquire, Variable v
where leaks_on_some_path(acquire, v)
select acquire,
  "of_parse_phandle return stored in $@ may leak refcount: of_node_put not guaranteed on all paths to function exit.",
  v, v.getName()
