/**
 * @name Kstrdup memory leak (four-features / affs_remount pattern)
 * @description A kstrdup-allocated buffer stored in a local variable is
 *              never released via kfree on any path in the enclosing
 *              function. Modeled after the affs_remount bug fixed by
 *              upstream commit 450c3d416683.
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3-d5-l1-lu5
 */

import cpp

predicate isKstrdupAlloc(FunctionCall fc, Variable v) {
  fc.getTarget().getName() = "kstrdup" and
  (
    exists(AssignExpr ae |
      ae.getRValue() = fc and
      ae.getLValue() = v.getAnAccess()
    )
    or
    exists(Initializer init |
      init.getExpr() = fc and
      init.getDeclaration() = v
    )
  )
}

predicate hasFreeOfVar(Function fn, Variable v) {
  exists(FunctionCall kf |
    kf.getTarget().getName() = "kfree" and
    kf.getEnclosingFunction() = fn and
    kf.getArgument(0) = v.getAnAccess()
  )
}

from FunctionCall alloc, Variable v, Function fn
where
  isKstrdupAlloc(alloc, v) and
  fn = alloc.getEnclosingFunction() and
  not hasFreeOfVar(fn, v)
select alloc,
  "kstrdup result stored in $@ is never kfree'd on any path in " + fn.getName() +
    " (possible memory leak).",
  v, v.getName()
