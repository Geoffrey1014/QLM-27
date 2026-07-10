/**
 * @name Allocated buffer leaks via early bare return that bypasses error label
 * @description A local pointer variable holds the result of an allocation-style
 *              call (kmalloc/kzalloc/kcalloc/malloc/...). The enclosing function
 *              contains an error-exit label that frees that pointer
 *              (kfree/free), reached normally via `goto`. A bare `return` on
 *              some control path after a non-null use of the buffer bypasses
 *              that cleanup label and leaks the buffer.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-lu-2
 */

import cpp

/** A function-call name considered an "allocator" returning a pointer that
 *  must be released on every error path. */
bindingset[n]
predicate isAllocName(string n) {
  n = "kmalloc" or
  n = "kzalloc" or
  n = "kcalloc" or
  n = "kmalloc_array" or
  n = "kmemdup" or
  n = "kstrdup" or
  n = "vmalloc" or
  n = "vzalloc" or
  n = "malloc" or
  n = "calloc" or
  n = "realloc"
}

/** A function-call name considered a "release" for an allocator result. */
bindingset[n]
predicate isReleaseName(string n) {
  n = "kfree" or
  n = "kvfree" or
  n = "vfree" or
  n = "free"
}

/** A call that releases variable `v` (passes `v` as an argument). */
predicate releasesVar(FunctionCall fc, Variable v) {
  isReleaseName(fc.getTarget().getName()) and
  fc.getAnArgument() = v.getAnAccess()
}

/** A "non-null-check" use of `v`: a variable access that is NOT inside the
 *  condition of an `if` whose condition is just `!v` / `v == 0` / `v == NULL`.
 *  In practice we approximate: an access of `v` that is passed as an argument
 *  to a call, or whose parent expression is a pointer dereference, or any
 *  access not directly under a NotExpr / EQExpr at the top of an IfStmt cond.
 */
predicate isNonNullCheckUse(VariableAccess va, Variable v) {
  va = v.getAnAccess() and
  (
    exists(FunctionCall c | c.getAnArgument() = va)
    or
    exists(PointerDereferenceExpr d | d.getOperand() = va)
    or
    exists(Assignment a | a.getRValue() = va)
  )
}

from
  Function f, LocalVariable v, AssignExpr ae, FunctionCall alloc,
  ReturnStmt badRet, FunctionCall release, VariableAccess use
where
  // The allocation: v = alloc(...)
  ae.getEnclosingFunction() = f and
  ae.getLValue() = v.getAnAccess() and
  ae.getRValue() = alloc and
  isAllocName(alloc.getTarget().getName()) and
  v.getType().getUnspecifiedType() instanceof PointerType and
  // There exists a release of v inside the same function (the cleanup site).
  releasesVar(release, v) and
  release.getEnclosingFunction() = f and
  // The bad return is in this function and reachable from the allocation.
  badRet.getEnclosingFunction() = f and
  ae.getASuccessor+() = badRet and
  // No release of v on the path from allocation to bad return.
  not exists(FunctionCall r2 |
    releasesVar(r2, v) and
    r2.getEnclosingFunction() = f and
    ae.getASuccessor+() = r2 and
    r2.getASuccessor+() = badRet
  ) and
  // There is some non-null-check use of v on the path from allocation to
  // bad return — i.e. the program already relied on v being valid, so the
  // bad return is on a post-success path.
  isNonNullCheckUse(use, v) and
  ae.getASuccessor+() = use and
  use.getASuccessor+() = badRet
select badRet,
  "Bare 'return' after allocation of '" + v.getName() +
    "' at $@ leaks the buffer: no release of '" + v.getName() +
    "' on this path, but a cleanup call $@ exists elsewhere in this function.",
  ae, "allocation",
  release, "cleanup site bypassed"
