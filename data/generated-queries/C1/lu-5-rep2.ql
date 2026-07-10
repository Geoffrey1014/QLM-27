/**
 * @name Allocated buffer leaked on some return paths
 * @description A local pointer is initialized from an allocator (e.g. kstrdup,
 *              kmalloc) and is freed only on a subset of the function's return
 *              paths, causing a memory leak on the remaining returns.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-lu-5
 */

import cpp

/** Allocator-like calls whose return value owns memory that must be freed. */
predicate isAllocCall(FunctionCall fc) {
  fc.getTarget().getName() = "kstrdup" or
  fc.getTarget().getName() = "kmalloc" or
  fc.getTarget().getName() = "kzalloc" or
  fc.getTarget().getName() = "kcalloc" or
  fc.getTarget().getName() = "kmemdup" or
  fc.getTarget().getName() = "vmalloc" or
  fc.getTarget().getName() = "vzalloc" or
  fc.getTarget().getName() = "strdup" or
  fc.getTarget().getName() = "malloc"
}

/** Deallocator-like calls. */
predicate isFreeCall(FunctionCall fc, Variable v) {
  (fc.getTarget().getName() = "kfree" or
   fc.getTarget().getName() = "kvfree" or
   fc.getTarget().getName() = "vfree" or
   fc.getTarget().getName() = "free") and
  fc.getArgument(0) = v.getAnAccess()
}

/** Holds if the function has at least one ReturnStmt that is not preceded
 *  (in the same function) by a free of v. */
predicate hasUnfreedReturn(Function f, Variable v) {
  exists(ReturnStmt rs |
    rs.getEnclosingFunction() = f and
    not exists(FunctionCall freec |
      freec.getEnclosingFunction() = f and
      isFreeCall(freec, v) and
      freec.getLocation().getStartLine() < rs.getLocation().getStartLine()
    )
  )
}

/** Holds if v has at least one free in the function. */
predicate hasSomeFree(Function f, Variable v) {
  exists(FunctionCall freec |
    freec.getEnclosingFunction() = f and
    isFreeCall(freec, v)
  )
}

from Function f, LocalVariable v, FunctionCall alloc
where
  alloc.getEnclosingFunction() = f and
  isAllocCall(alloc) and
  // v is assigned the result of the allocator (either initializer or assignment)
  (
    v.getInitializer().getExpr() = alloc
    or
    exists(AssignExpr ae |
      ae.getEnclosingFunction() = f and
      ae.getLValue() = v.getAnAccess() and
      ae.getRValue() = alloc
    )
  ) and
  // at least one free of v exists (so this is a managed resource)
  hasSomeFree(f, v) and
  // and at least one return path that is not preceded by a free of v
  hasUnfreedReturn(f, v)
select alloc,
  "Allocation assigned to '" + v.getName() +
  "' may leak: some return paths in $@ do not free it.",
  f, f.getName()
