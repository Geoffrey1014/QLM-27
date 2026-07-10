/**
 * @name Missing kfree on some return path after kstrdup-family allocation
 * @description A kstrdup/kmemdup/kstrndup-family call stores a freshly
 *              allocated buffer in a local variable. If the enclosing
 *              function has at least one return statement that is not
 *              preceded (dominated) by a kfree() of that variable on every
 *              path, the buffer leaks on that return (CWE-401).
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-lu-5
 */

import cpp

/* Allocator APIs that return a heap-allocated buffer the caller owns. */
predicate isAllocApi(string name) {
  name = "kstrdup" or
  name = "kstrndup" or
  name = "kmemdup" or
  name = "kmemdup_nul" or
  name = "kstrdup_const" or
  name = "kasprintf" or
  name = "kvasprintf"
}

/* Release calls that free a heap buffer. */
predicate isReleaseCall(FunctionCall c) {
  c.getTarget().getName() = "kfree" or
  c.getTarget().getName() = "kvfree" or
  c.getTarget().getName() = "kfree_const" or
  c.getTarget().getName() = "kfree_sensitive"
}

/* The variable that receives the call's return value: either via an
 * initializer (`T *v = alloc(...);`) or an assignment (`v = alloc(...);`). */
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

/* A release call whose first argument reads `v`. */
predicate isReleaseOfVar(FunctionCall rel, Variable v) {
  isReleaseCall(rel) and
  rel.getArgument(0).(VariableAccess).getTarget() = v
}

/* True if every control-flow path from `acquire` to `ret` passes through a
 * release call on `v`. We approximate "every path" by requiring that the
 * release strictly dominates `ret` in the enclosing function's CFG. */
predicate releaseDominatesReturn(FunctionCall acquire, Variable v, ReturnStmt ret) {
  exists(FunctionCall rel |
    isReleaseOfVar(rel, v) and
    rel.getEnclosingFunction() = ret.getEnclosingFunction() and
    /* `rel` reachable from `acquire` and dominates `ret` */
    rel.getAPredecessor*() = acquire and
    ret.getAPredecessor+() = rel
  )
}

from FunctionCall acquire, Variable v, Function f, ReturnStmt ret
where
  isAllocApi(acquire.getTarget().getName()) and
  v = getReceiverVariable(acquire) and
  f = acquire.getEnclosingFunction() and
  ret.getEnclosingFunction() = f and
  /* this return is reachable after the acquire */
  ret.getAPredecessor+() = acquire and
  /* and there is NO release of `v` on its path */
  not releaseDominatesReturn(acquire, v, ret)
select acquire,
  "Call to " + acquire.getTarget().getName() +
    " stores an allocated buffer in '" + v.getName() +
    "' but at least one return in this function ($@) is reached without a kfree() of it -- possible leak.",
  ret, "this return"
