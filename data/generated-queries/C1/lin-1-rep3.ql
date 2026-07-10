/**
 * @name Missing of_node_put on early loop exit after of_parse_phandle
 * @description Detects refcounted device_node acquisition (of_parse_phandle and
 *              similar OF acquire APIs) whose result is stored in a local
 *              variable, then on some control-flow path the loop iteration
 *              terminates (via continue, break, return, or goto) without a
 *              call to the matching release API (of_node_put) on that variable.
 *              This pattern matches resource-leak fixes such as commit
 *              74139a64e8ce.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-lin-1
 */

import cpp

/* Refcounted acquire APIs that return a device_node-like handle. */
predicate isOfAcquireApi(string name) {
  name = "of_parse_phandle" or
  name = "of_find_node_by_path" or
  name = "of_find_node_opts_by_path" or
  name = "of_find_matching_node" or
  name = "of_find_compatible_node" or
  name = "of_find_node_by_name" or
  name = "of_get_child_by_name" or
  name = "of_get_next_child" or
  name = "of_get_next_available_child" or
  name = "of_get_parent" or
  name = "of_get_next_parent"
}

/* Matching release API. */
predicate isOfReleaseApi(string name) { name = "of_node_put" }

/* True if `release` is a call to of_node_put on the same local variable
 * holding the acquired handle. */
predicate releasesVar(FunctionCall release, Variable v) {
  isOfReleaseApi(release.getTarget().getName()) and
  exists(VariableAccess va |
    va = release.getArgument(0).getAChild*() or
    va = release.getArgument(0)
  |
    va.getTarget() = v
  )
}

/* A loop-exiting statement that terminates the current iteration without
 * normal fall-through to the loop's "after-body" cleanup region. */
predicate isLoopExitStmt(Stmt s) {
  s instanceof ContinueStmt or
  s instanceof BreakStmt or
  s instanceof ReturnStmt or
  s instanceof GotoStmt
}

/* The acquire-call assigns its result to a local Variable v inside a loop. */
predicate acquireInLoop(FunctionCall acquire, Variable v, Loop loop) {
  isOfAcquireApi(acquire.getTarget().getName()) and
  exists(Expr lhs, AssignExpr a |
    a.getRValue() = acquire and a.getLValue() = lhs
  |
    lhs.(VariableAccess).getTarget() = v
  ) and
  loop.getStmt().getAChild*() = acquire.getEnclosingStmt()
}

/* The exit statement is reachable after the acquire inside the same loop,
 * and there is no of_node_put(v) on the path from acquire to that exit. */
predicate leakingExit(FunctionCall acquire, Variable v, Loop loop, Stmt exit) {
  acquireInLoop(acquire, v, loop) and
  isLoopExitStmt(exit) and
  loop.getStmt().getAChild*() = exit and
  /* exit is control-flow reachable from acquire */
  acquire.getASuccessor+() = exit and
  /* no release of v on any path between acquire and exit */
  not exists(FunctionCall rel |
    releasesVar(rel, v) and
    acquire.getASuccessor+() = rel and
    rel.getASuccessor+() = exit
  ) and
  /* the exit is not itself preceded immediately by a release in same basic block path */
  not exists(FunctionCall rel |
    releasesVar(rel, v) and
    rel.getEnclosingStmt().getParentStmt*() = exit.getParentStmt*()
    and rel.getLocation().getStartLine() < exit.getLocation().getStartLine()
    and rel.getEnclosingFunction() = exit.getEnclosingFunction()
    and not exists(FunctionCall rel2 |
      releasesVar(rel2, v) and rel2 = rel
      and rel.getASuccessor+() = exit
      and exists(FunctionCall acq2 | acq2 = acquire and acq2.getASuccessor+() = rel)
    ) and
    rel.getASuccessor*() = exit
  )
}

from FunctionCall acquire, Variable v, Loop loop, Stmt exit, Function f
where
  leakingExit(acquire, v, loop, exit) and
  f = acquire.getEnclosingFunction() and
  exit.getEnclosingFunction() = f and
  /* require that the function does contain at least one release of v somewhere
   * (otherwise it's a totally different bug shape — we want missing-on-some-path) */
  exists(FunctionCall anyRel | releasesVar(anyRel, v) and anyRel.getEnclosingFunction() = f)
  or
  /* OR: no release at all in the function (pure leak) */
  acquireInLoop(acquire, v, loop) and
  exit = loop.getStmt() and
  not exists(FunctionCall anyRel |
    isOfReleaseApi(anyRel.getTarget().getName()) and
    anyRel.getEnclosingFunction() = acquire.getEnclosingFunction()
  ) and
  f = acquire.getEnclosingFunction()
select acquire,
  "Refcounted device_node acquired by $@ may leak: control flow can reach " +
  "a loop-exit ($@) without a matching of_node_put on variable '" + v.getName() + "'.",
  acquire.getTarget(), acquire.getTarget().getName(),
  exit, "exit"
