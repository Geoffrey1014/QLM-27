/**
 * @name Allocated string/buffer not freed on all paths after early-return
 * @description Detects a local pointer variable assigned the result of an
 *              allocation API (e.g. kstrdup/kmalloc/kzalloc) where at
 *              least one return statement reachable from the allocation
 *              does NOT free the variable, while at least one other
 *              reachable return path DOES free it. This typically
 *              indicates a missing kfree on a success or early-exit path.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-lu-5
 */

import cpp

predicate isAllocApi(string name) {
  name = "kstrdup" or
  name = "kstrndup" or
  name = "kmemdup" or
  name = "kmalloc" or
  name = "kzalloc" or
  name = "kcalloc" or
  name = "kvmalloc" or
  name = "kvzalloc" or
  name = "vmalloc" or
  name = "vzalloc"
}

predicate isFreeApi(string name) {
  name = "kfree" or
  name = "kvfree" or
  name = "vfree" or
  name = "kzfree"
}

/* The variable v is freed on the path of return statement r:
 * some call to a free API takes v (or an access to v) as argument,
 * the call's basic block reaches the return's basic block, and the
 * call appears before the return in execution order. */
predicate freedBeforeReturn(LocalVariable v, ReturnStmt r) {
  exists(FunctionCall fc |
    isFreeApi(fc.getTarget().getName()) and
    fc.getAnArgument() = v.getAnAccess() and
    fc.getEnclosingFunction() = r.getEnclosingFunction() and
    (
      fc.getASuccessor+() = r
      or
      fc.getEnclosingStmt().getASuccessor*() = r
    )
  )
}

/* return r is reachable from the allocation assignment to v (i.e. flows
 * past the allocation). */
predicate returnReachableFromAlloc(LocalVariable v, FunctionCall alloc, ReturnStmt r) {
  exists(Expr assignSite |
    assignSite = v.getInitializer().getExpr()
    or
    exists(AssignExpr ae |
      ae.getLValue() = v.getAnAccess() and
      assignSite = ae
    )
  |
    assignSite = alloc or assignSite.getAChild*() = alloc
  ) and
  alloc.getEnclosingFunction() = r.getEnclosingFunction() and
  (alloc.getASuccessor+() = r or alloc.getEnclosingStmt().getASuccessor*() = r)
}

from Function f, LocalVariable v, FunctionCall alloc, ReturnStmt rLeak, ReturnStmt rOk
where
  f = alloc.getEnclosingFunction() and
  isAllocApi(alloc.getTarget().getName()) and
  v.getFunction() = f and
  (
    v.getInitializer().getExpr() = alloc
    or
    exists(AssignExpr ae |
      ae.getLValue() = v.getAnAccess() and ae.getRValue() = alloc
    )
  ) and
  rLeak.getEnclosingFunction() = f and
  rOk.getEnclosingFunction() = f and
  rLeak != rOk and
  returnReachableFromAlloc(v, alloc, rLeak) and
  returnReachableFromAlloc(v, alloc, rOk) and
  not freedBeforeReturn(v, rLeak) and
  freedBeforeReturn(v, rOk)
select rLeak,
  "Variable '" + v.getName() + "' allocated by " + alloc.getTarget().getName() +
  " at $@ is not freed on this return path, while another return path frees it ($@).",
  alloc, alloc.getTarget().getName(), rOk, "freed here"
