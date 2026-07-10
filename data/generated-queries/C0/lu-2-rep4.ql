/**
 * @name Memory leak: early return bypasses cleanup label
 * @description Finds functions that allocate a heap buffer with kmalloc/kzalloc/kcalloc/
 *              kmemdup/kstrdup family, install a cleanup label (e.g. `err:`/`out:`) that
 *              frees the buffer via kfree, but contain an early `return` statement
 *              between the allocation and the cleanup label that bypasses the kfree,
 *              causing a memory leak on that path.
 * @kind problem
 * @problem.severity warning
 * @id cpp/early-return-bypasses-kfree-cleanup
 * @tags correctness
 *       memory-leak
 */

import cpp

/** A kernel heap-allocation function whose return value must eventually be kfree'd. */
predicate isKernelAllocFunc(Function f) {
  f.getName() =
    [
      "kmalloc", "kzalloc", "kcalloc", "kmalloc_array", "kvmalloc", "kvzalloc",
      "kvcalloc", "kvmalloc_array", "kmemdup", "kmemdup_nul", "kstrdup",
      "kstrndup", "krealloc", "devm_kmalloc_not_used_just_to_avoid_match"
    ]
}

/** A kfree-family release. */
predicate isKfreeFunc(Function f) {
  f.getName() = ["kfree", "kvfree", "kzfree", "kfree_sensitive"]
}

/** A call to a kernel allocator whose return is stored in `v`. */
predicate allocAssignedTo(LocalVariable v, FunctionCall alloc) {
  isKernelAllocFunc(alloc.getTarget()) and
  exists(AssignExpr a |
    a.getLValue() = v.getAnAccess() and
    a.getRValue() = alloc
  )
  or
  isKernelAllocFunc(alloc.getTarget()) and
  v.getInitializer().getExpr() = alloc
}

/** A statement that frees `v`. */
predicate freesVar(Stmt s, LocalVariable v) {
  exists(FunctionCall fc |
    fc.getEnclosingStmt() = s and
    isKfreeFunc(fc.getTarget()) and
    fc.getAnArgument() = v.getAnAccess()
  )
  or
  // also accept any descendant statement
  exists(FunctionCall fc |
    isKfreeFunc(fc.getTarget()) and
    fc.getAnArgument() = v.getAnAccess() and
    s.getAChild*() = fc.getEnclosingStmt()
  )
}

/** A labeled cleanup statement that frees `v`. */
predicate isCleanupLabel(LabelStmt lbl, LocalVariable v) {
  exists(Stmt body |
    body = lbl.getEnclosingBlock().getAChild*() and
    freesVar(body, v)
  )
}

/** A return statement that does NOT itself free `v`. */
predicate isLeakyReturn(ReturnStmt r, LocalVariable v) {
  not exists(FunctionCall fc |
    isKfreeFunc(fc.getTarget()) and
    fc.getAnArgument() = v.getAnAccess() and
    fc.getEnclosingStmt().getParentStmt*() = r.getParentStmt*()
  )
}

from
  Function f, LocalVariable buf, FunctionCall alloc, LabelStmt cleanup, ReturnStmt early
where
  // buffer is allocated in f
  alloc.getEnclosingFunction() = f and
  allocAssignedTo(buf, alloc) and
  buf.getFunction() = f and
  // there is a cleanup label in f that frees the buffer
  cleanup.getEnclosingFunction() = f and
  isCleanupLabel(cleanup, buf) and
  // there is a return statement in f, after the alloc, before the cleanup label,
  // that does not free the buffer
  early.getEnclosingFunction() = f and
  isLeakyReturn(early, buf) and
  early.getLocation().getStartLine() > alloc.getLocation().getStartLine() and
  early.getLocation().getStartLine() < cleanup.getLocation().getStartLine() and
  // the cleanup label is reached via `goto` somewhere in the function
  exists(GotoStmt g |
    g.getEnclosingFunction() = f and
    g.getName() = cleanup.getName()
  )
select early,
  "Early return in function $@ bypasses cleanup label '" + cleanup.getName() +
    "' which frees buffer '" + buf.getName() + "' allocated at $@; possible memory leak.",
  f, f.getName(), alloc, "allocation"
