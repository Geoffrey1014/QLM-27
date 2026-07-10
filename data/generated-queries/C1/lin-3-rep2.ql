/**
 * @name Missing of_node_put on early-return path after of_parse_phandle
 * @description A device_node acquired via an of_parse_phandle-style API has its
 *              refcount incremented. If the function returns early on an error
 *              path before calling of_node_put, the node refcount leaks.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-lin-3
 */

import cpp

/* Acquire APIs that bump a device_node refcount and return the node. */
predicate isAcquireApi(string name) {
  name = "of_parse_phandle" or
  name = "of_parse_phandle_with_args" or
  name = "of_parse_phandle_with_fixed_args" or
  name = "of_get_child_by_name" or
  name = "of_get_next_child" or
  name = "of_get_next_available_child" or
  name = "of_get_parent" or
  name = "of_get_next_parent" or
  name = "of_find_node_by_path" or
  name = "of_find_node_by_name" or
  name = "of_find_compatible_node" or
  name = "of_find_matching_node" or
  name = "of_find_matching_node_and_match"
}

/* Release API for a device_node. */
predicate isReleaseApi(string name) {
  name = "of_node_put"
}

/*
 * Recognize a return-stmt that aborts the enclosing function. We treat any
 * ReturnStmt as such, but require it lexically follows the acquire and that
 * no of_node_put on the acquired node occurs between the acquire and the
 * return on the source-text path.
 */
from
  FunctionCall acq, LocalVariable v, Function enclosing,
  ReturnStmt ret, Location aloc, Location rloc
where
  isAcquireApi(acq.getTarget().getName()) and
  enclosing = acq.getEnclosingFunction() and
  /* The acquired node is assigned into a local variable v, either via direct
   * initialization or an assignment. */
  (
    v.getInitializer().getExpr() = acq
    or
    exists(AssignExpr a |
      a.getRValue() = acq and
      a.getLValue() = v.getAnAccess()
    )
  ) and
  ret.getEnclosingFunction() = enclosing and
  aloc = acq.getLocation() and
  rloc = ret.getLocation() and
  /* Return is after the acquire in the same function. */
  rloc.getStartLine() > aloc.getStartLine() and
  /* No release of v occurs between the acquire and the return (text order). */
  not exists(FunctionCall rel, Location relLoc |
    isReleaseApi(rel.getTarget().getName()) and
    rel.getEnclosingFunction() = enclosing and
    relLoc = rel.getLocation() and
    relLoc.getStartLine() > aloc.getStartLine() and
    relLoc.getStartLine() < rloc.getStartLine() and
    rel.getAnArgument() = v.getAnAccess()
  ) and
  /* No release of v on or after the return up to the function end either
   * (the early return cannot reach a later cleanup). We approximate by
   * checking there is no release of v *anywhere strictly between* acquire
   * and return; we additionally require the return itself does not pass v
   * to a release (rare, but guards against `return of_node_put(v), -ENOMEM`
   * style hacks). */
  not exists(FunctionCall rel |
    isReleaseApi(rel.getTarget().getName()) and
    rel.getEnclosingFunction() = enclosing and
    ret = ret and
    rel.getParent*() = ret and
    rel.getAnArgument() = v.getAnAccess()
  ) and
  /* The return must be guarded by an IfStmt whose condition references some
   * value computed after the acquire (typical error check) — this avoids
   * flagging the unconditional final return of a function. */
  exists(IfStmt ifs |
    ifs.getEnclosingFunction() = enclosing and
    ret.getParent*() = ifs and
    ifs.getLocation().getStartLine() > aloc.getStartLine() and
    ifs.getLocation().getStartLine() < rloc.getStartLine()
    or
    ret.getParent*() = ifs and
    ifs.getEnclosingFunction() = enclosing and
    ifs.getLocation().getStartLine() >= aloc.getStartLine()
  )
select acq,
  "Resource acquired here (" + acq.getTarget().getName() +
    ") may leak: no matching release before early return at line " +
    rloc.getStartLine() + "."
