/**
 * @name Allocated buffer leaked on at least one return path
 * @description A heap allocator (kstrdup / kmalloc / kzalloc / kcalloc /
 *              kmemdup) returns a pointer that is stored in a local
 *              variable, but the enclosing function returns through a
 *              path on which the variable is never released via
 *              kfree() (or its variants). The release exists on some
 *              path (typically the error path), but at least one
 *              return statement is reached without going through any
 *              release of the variable -- the classic resource-leak
 *              shape (CWE-401) seen in remount / setup / probe
 *              helpers that only free on the error path.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-lu-5
 */

import cpp

/** Heap allocators whose return value the caller owns. */
predicate isAllocApi(string name) {
  name = "kstrdup" or
  name = "kstrndup" or
  name = "kmemdup" or
  name = "kmalloc" or
  name = "kzalloc" or
  name = "kcalloc" or
  name = "krealloc" or
  name = "vmalloc" or
  name = "vzalloc"
}

/** True if `c` is a call to a kfree-family release. */
predicate isFreeCall(FunctionCall c) {
  c.getTarget().getName() = "kfree" or
  c.getTarget().getName() = "kvfree" or
  c.getTarget().getName() = "kzfree" or
  c.getTarget().getName() = "kfree_sensitive" or
  c.getTarget().getName() = "vfree"
}

/**
 * The local variable that captures the return value of `call`, either
 * via initialiser (`T *v = call(...)`) or via assignment
 * (`v = call(...)`).
 */
LocalVariable allocReceiverVariable(FunctionCall call) {
  exists(LocalVariable v |
    v.getInitializer().getExpr() = call and
    result = v
  )
  or
  exists(AssignExpr a, VariableAccess lhs, LocalVariable v |
    a.getRValue() = call and
    lhs = a.getLValue() and
    v = lhs.getTarget() and
    result = v
  )
}

/** A kfree-family call inside `f` whose first argument is a read of `v`. */
predicate isFreeOf(FunctionCall fr, Function f, LocalVariable v) {
  isFreeCall(fr) and
  fr.getEnclosingFunction() = f and
  exists(VariableAccess arg |
    arg = fr.getArgument(0) and arg.getTarget() = v
  )
}

/** True iff at least one kfree(v) exists in `f`. */
predicate freesVariable(Function f, LocalVariable v) {
  exists(FunctionCall fr | isFreeOf(fr, f, v))
}

/**
 * A return statement `r` in `f` is "leaky" with respect to local `v`
 * if the entry to the basic block containing `r` is reachable from
 * the function entry without passing through any basic block that
 * contains a kfree(v) call. I.e., the kfree does not dominate the
 * return. We use the CFG dominance reachability via BasicBlock.
 */
predicate hasLeakingReturn(Function f, LocalVariable v) {
  exists(ReturnStmt r, BasicBlock rbb |
    r.getEnclosingFunction() = f and
    rbb = r.getBasicBlock() and
    not exists(FunctionCall fr, BasicBlock fbb |
      isFreeOf(fr, f, v) and
      fbb = fr.getBasicBlock() and
      bbDominates(fbb, rbb)
    )
  )
}

from FunctionCall acquire, LocalVariable recv, Function enclosing
where
  isAllocApi(acquire.getTarget().getName()) and
  recv = allocReceiverVariable(acquire) and
  enclosing = acquire.getEnclosingFunction() and
  freesVariable(enclosing, recv) and
  hasLeakingReturn(enclosing, recv)
select acquire,
  "Allocation via " + acquire.getTarget().getName() +
    " stored in local '" + recv.getName() +
    "' is freed on some paths but at least one return in '" +
    enclosing.getName() + "' is not dominated by the kfree -- possible leak."
