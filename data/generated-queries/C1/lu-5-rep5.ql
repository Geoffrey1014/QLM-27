/**
 * @name Leaked kstrdup/kmalloc result on a function exit path
 * @description A local pointer variable receives the result of a
 *              kernel allocation routine (kstrdup / kmalloc / kzalloc
 *              / kcalloc). Some return statement in the enclosing
 *              function is reachable without the variable having
 *              been freed via kfree on that path, while another
 *              return path *does* free it. This asymmetric handling
 *              is the classic resource-leak shape exemplified by the
 *              affs_remount fix (450c3d416683): the success-path
 *              return leaks the strdup'd options buffer while the
 *              parse-options-failure path correctly kfrees it.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-lu-5
 */

import cpp

/* Recognised acquisition routines whose return value, when stored
 * into a local pointer, must be released with kfree on every exit
 * path of the enclosing function. The list is deliberately small to
 * keep precision high; kstrdup is the one exercised by the seed.
 */
predicate isAllocCall(FunctionCall fc) {
  fc.getTarget().getName() = "kstrdup" or
  fc.getTarget().getName() = "kstrdup_const" or
  fc.getTarget().getName() = "kmemdup" or
  fc.getTarget().getName() = "kmalloc" or
  fc.getTarget().getName() = "kzalloc" or
  fc.getTarget().getName() = "kcalloc" or
  fc.getTarget().getName() = "malloc"
}

/* True if `fc` is a kfree (or related release) called on `v` (i.e.
 * one of its arguments is a read of `v`). */
predicate freesVar(FunctionCall fc, LocalVariable v) {
  (fc.getTarget().getName() = "kfree" or
   fc.getTarget().getName() = "kvfree" or
   fc.getTarget().getName() = "kfree_const" or
   fc.getTarget().getName() = "free") and
  fc.getAnArgument().(VariableAccess).getTarget() = v
}

from
  Function f, LocalVariable v, FunctionCall acquire,
  ReturnStmt rLeak, ReturnStmt rOk, FunctionCall release
where
  /* The variable is local to f and receives an allocation. */
  v.getFunction() = f and
  acquire.getEnclosingFunction() = f and
  isAllocCall(acquire) and
  (
    /* Either via direct assignment `v = alloc()` */
    exists(AssignExpr a |
      a.getEnclosingFunction() = f and
      a.getLValue().(VariableAccess).getTarget() = v and
      a.getRValue() = acquire
    )
    or
    /* Or via initializer `T *v = alloc()` */
    exists(Initializer ini |
      ini.getDeclaration() = v and
      ini.getExpr() = acquire
    )
  ) and
  /* Some return in f *does* free v before returning — establishing
   * the asymmetric-cleanup shape. */
  rOk.getEnclosingFunction() = f and
  release.getEnclosingFunction() = f and
  freesVar(release, v) and
  release.getLocation().getStartLine() < rOk.getLocation().getStartLine() and
  /* Another return path exits f without any kfree of v dominating it
   * lexically (cheap proxy: no kfree(v) appears on any source line
   * preceding rLeak inside f). */
  rLeak.getEnclosingFunction() = f and
  rLeak != rOk and
  not exists(FunctionCall rel2 |
    freesVar(rel2, v) and
    rel2.getEnclosingFunction() = f and
    rel2.getLocation().getStartLine() < rLeak.getLocation().getStartLine() and
    /* the freeing call must lie on the same control-flow chain as
     * the leaking return; approximate by requiring it not to be the
     * one belonging to the other exit path. */
    rel2.getLocation().getStartLine() > acquire.getLocation().getStartLine()
  ) and
  /* The leaking return must come *after* the allocation (otherwise
   * v is uninitialised on that path and not a leak). */
  rLeak.getLocation().getStartLine() > acquire.getLocation().getStartLine()
select rLeak,
  "Possible leak of allocation made at $@ stored in '" + v.getName() +
  "'; this return path does not release it, while another path does (see $@).",
  acquire, acquire.getTarget().getName() + "()",
  release, "kfree call"
