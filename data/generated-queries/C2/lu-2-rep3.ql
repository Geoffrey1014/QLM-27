/**
 * @name  rq3-c2-lu-2-rep3
 * @id    cpp/rq3/c2/lu-2-rep3
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects memory leaks where a buffer allocated by kmalloc/kzalloc
 *              is freed at a cleanup label, but an early `return` on an error
 *              path bypasses that cleanup.
 */

import cpp

/** A call that allocates a kernel buffer requiring kfree. */
predicate isAllocCall(FunctionCall fc) {
  fc.getTarget().getName() = ["kmalloc", "kzalloc", "kcalloc", "kmemdup", "kstrdup"]
}

/** A call that releases a kernel buffer. */
predicate isFreeCall(FunctionCall fc, Variable v) {
  fc.getTarget().getName() = ["kfree", "kvfree", "kzfree"] and
  fc.getArgument(0) = v.getAnAccess()
}

/** `v` is assigned the result of an allocation call inside function `f`. */
predicate allocatedVar(Function f, Variable v, FunctionCall alloc) {
  isAllocCall(alloc) and
  alloc.getEnclosingFunction() = f and
  (
    exists(AssignExpr ae |
      ae.getEnclosingFunction() = f and
      ae.getRValue() = alloc and
      ae.getLValue() = v.getAnAccess()
    )
    or
    exists(Initializer init |
      init.getExpr() = alloc and
      init.getDeclaration() = v
    )
  )
}

/** Function `f` has a cleanup-style free of `v` (typically under an `err:` label). */
predicate hasCleanupFree(Function f, Variable v, FunctionCall freeCall) {
  isFreeCall(freeCall, v) and
  freeCall.getEnclosingFunction() = f
}

/**
 * `ret` is an early `return` statement in `f` that occurs on a control-flow path
 * starting after the allocation of `v` but does not transfer control through
 * the cleanup free of `v`.
 */
predicate earlyReturnBypassesFree(
  Function f, Variable v, FunctionCall alloc, ReturnStmt ret, FunctionCall freeCall
) {
  allocatedVar(f, v, alloc) and
  hasCleanupFree(f, v, freeCall) and
  ret.getEnclosingFunction() = f and
  ret != freeCall.getEnclosingStmt() and
  // The return is reachable from the allocation.
  alloc.getASuccessor+() = ret and
  // The return does NOT reach the free along CFG successors.
  not ret.getASuccessor*() = freeCall
}

from Function f, Variable v, FunctionCall alloc, ReturnStmt ret, FunctionCall freeCall
where earlyReturnBypassesFree(f, v, alloc, ret, freeCall)
select ret,
  "Memory leak: early return in $@ bypasses cleanup free of '" + v.getName() + "' allocated at $@.",
  f, f.getName(), alloc, "allocation"
