/**
 * @name  rq3-c2-lin-1-rep4
 * @id    cpp/rq3/c2/lin-1-rep4
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2: detect of_parse_phandle results not released by of_node_put on all paths.
 */

import cpp

/** Holds if `c` is a call to `of_parse_phandle` whose result is assigned to local variable `v`. */
predicate acquires_node(FunctionCall c, LocalScopeVariable v) {
  c.getTarget().hasName("of_parse_phandle") and
  exists(AssignExpr a |
    a.getRValue() = c and
    a.getLValue() = v.getAnAccess()
  )
}

/** Holds if `c` is a call to `of_node_put(v)` releasing the local variable `v`. */
predicate releases_node(FunctionCall c, LocalScopeVariable v) {
  c.getTarget().hasName("of_node_put") and
  c.getArgument(0) = v.getAnAccess()
}

/** Holds if the function `f` contains an acquisition of `v` via `of_parse_phandle`
 *  but contains no release of `v` via `of_node_put` (intra-procedural under-approx). */
predicate function_acquires_but_never_releases(Function f, LocalScopeVariable v, FunctionCall acq) {
  acquires_node(acq, v) and
  acq.getEnclosingFunction() = f and
  v.getFunction() = f and
  not exists(FunctionCall rel |
    releases_node(rel, v) and rel.getEnclosingFunction() = f
  )
}

/** Holds if the function has acquire + release but at least one early-exit (break/continue/return)
 *  statement reachable from the acquire that bypasses the release. Conservative path check. */
predicate has_release_bypass(Function f, LocalScopeVariable v, FunctionCall acq) {
  acquires_node(acq, v) and
  acq.getEnclosingFunction() = f and
  v.getFunction() = f and
  exists(FunctionCall rel | releases_node(rel, v) and rel.getEnclosingFunction() = f) and
  exists(Stmt s |
    s.getEnclosingFunction() = f and
    (
      s instanceof ContinueStmt or
      s instanceof BreakStmt or
      s instanceof ReturnStmt
    ) and
    // s is in the same loop as the acquisition
    exists(Loop l |
      l.getAChild*() = acq.getEnclosingStmt() and
      l.getAChild*() = s
    ) and
    // and there is no release dominating this exit statement in the same loop
    not exists(FunctionCall rel, Loop l2 |
      releases_node(rel, v) and
      rel.getEnclosingFunction() = f and
      l2.getAChild*() = rel.getEnclosingStmt() and
      l2.getAChild*() = s and
      rel.getLocation().getStartLine() < s.getLocation().getStartLine()
    )
  )
}

/** Top-level predicate: the variable `v` acquired at `acq` may leak. */
predicate unhandled_acquire(Function f, LocalScopeVariable v, FunctionCall acq) {
  function_acquires_but_never_releases(f, v, acq)
  or
  has_release_bypass(f, v, acq)
}

from Function f, LocalScopeVariable v, FunctionCall acq
where unhandled_acquire(f, v, acq)
select acq,
  "Possible reference leak: of_parse_phandle result assigned to '" + v.getName() +
    "' in function '" + f.getName() + "' may not be released by of_node_put on all paths."
