/**
 * @name  rq3-c2-lin-4-rep5
 * @id    cpp/rq3/c2/lin-4-rep5
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects of_parse_phandle refcount leaks where an error path
 *              returns without calling of_node_put on the acquired node.
 */

import cpp

/**
 * Holds if `acquire` is a call to of_parse_phandle whose result is assigned
 * to local variable `v` in function `f`.
 */
predicate acquires_node(FunctionCall acquire, Variable v, Function f) {
  acquire.getTarget().getName() = "of_parse_phandle" and
  acquire.getEnclosingFunction() = f and
  exists(AssignExpr a |
    a.getRValue() = acquire and
    a.getLValue() = v.getAnAccess()
  )
}

/**
 * Holds if `release` is a call to of_node_put applied to variable `v`
 * inside function `f`.
 */
predicate releases_node(FunctionCall release, Variable v, Function f) {
  release.getTarget().getName() = "of_node_put" and
  release.getEnclosingFunction() = f and
  release.getArgument(0) = v.getAnAccess()
}

/**
 * Holds if `ret` is a return statement in `f` that occurs on a path from
 * `acquire` (acquiring node into `v`) without any of_node_put on `v`
 * intervening between the acquire and the return.
 */
predicate early_return_without_release(ReturnStmt ret, FunctionCall acquire, Variable v, Function f) {
  acquires_node(acquire, v, f) and
  ret.getEnclosingFunction() = f and
  acquire.getASuccessor+() = ret and
  not exists(FunctionCall release |
    releases_node(release, v, f) and
    acquire.getASuccessor+() = release and
    release.getASuccessor+() = ret
  )
}

/**
 * Holds if function `f` acquires a node into variable `v` and has at least
 * one early-return path that leaks the refcount.
 */
predicate leaks_node_refcount(Function f, Variable v, FunctionCall acquire, ReturnStmt leakRet) {
  acquires_node(acquire, v, f) and
  early_return_without_release(leakRet, acquire, v, f)
}

from Function f, Variable v, FunctionCall acquire, ReturnStmt leakRet
where leaks_node_refcount(f, v, acquire, leakRet)
select leakRet,
  "Possible refcount leak: of_parse_phandle into $@ is not released by of_node_put before this return in " +
    f.getName() + ".", v, v.getName()
