/**
 * @name  rq3-c2-lu-5-rep5
 * @id    cpp/rq3/c2/lu-5-rep5
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects memory leaks where an allocation (e.g. kstrdup/kmalloc)
 *              is stored in a local variable but at least one return path
 *              within the function does not free it (modeled after affs_remount
 *              memory leak fix, commit 450c3d416683).
 */

import cpp

/**
 * Holds if `fc` is a call to a kernel allocation function whose return value
 * must eventually be freed by `kfree` (or a wrapper). We use the conservative
 * set of well-known allocators that pair with `kfree`.
 */
predicate isAllocCall(FunctionCall fc) {
  exists(string n | n = fc.getTarget().getName() |
    n = "kstrdup" or
    n = "kstrndup" or
    n = "kmemdup" or
    n = "kmalloc" or
    n = "kzalloc" or
    n = "kcalloc" or
    n = "krealloc"
  )
}

/**
 * Holds if `fc` is a call to a release function for memory that was returned
 * by an allocator from `isAllocCall`.
 */
predicate isFreeCall(FunctionCall fc) {
  exists(string n | n = fc.getTarget().getName() |
    n = "kfree" or
    n = "kvfree" or
    n = "kzfree"
  )
}

/**
 * Holds if local variable `v` in function `f` is assigned the result of an
 * allocation call `alloc`. We restrict to direct initializers and direct
 * assignments to keep things simple and conservative.
 */
predicate localGetsAlloc(Function f, LocalScopeVariable v, FunctionCall alloc) {
  isAllocCall(alloc) and
  alloc.getEnclosingFunction() = f and
  v.getFunction() = f and
  (
    // form: T *v = kstrdup(...)
    v.getInitializer().getExpr() = alloc
    or
    // form: v = kstrdup(...);
    exists(AssignExpr ae |
      ae.getEnclosingFunction() = f and
      ae.getRValue() = alloc and
      ae.getLValue() = v.getAnAccess()
    )
  )
}

/**
 * Holds if `fc` is a free call on the variable `v` inside function `f`.
 */
predicate freesVariable(Function f, LocalScopeVariable v, FunctionCall fc) {
  isFreeCall(fc) and
  fc.getEnclosingFunction() = f and
  fc.getArgument(0) = v.getAnAccess()
}

/**
 * Holds if `ret` is a return statement in `f` and no free of `v` is reachable
 * on the control-flow path from the allocation `alloc` to `ret` (we approximate
 * "no free on this path" by: there is no kfree(v) whose successor (in the CFG)
 * eventually reaches `ret`, while `alloc` does reach `ret`).
 *
 * We use the simple, sound-ish approximation: `alloc` reaches `ret`, and no
 * free-call on `v` exists between `alloc` and `ret` along a CFG path.
 */
predicate returnWithoutFree(
  Function f, LocalScopeVariable v, FunctionCall alloc, ReturnStmt ret
) {
  localGetsAlloc(f, v, alloc) and
  ret.getEnclosingFunction() = f and
  alloc.getASuccessor*() = ret and
  not exists(FunctionCall freeFc |
    freesVariable(f, v, freeFc) and
    alloc.getASuccessor*() = freeFc and
    freeFc.getASuccessor*() = ret
  )
}

from Function f, LocalScopeVariable v, FunctionCall alloc, ReturnStmt ret
where returnWithoutFree(f, v, alloc, ret)
select ret,
  "Potential memory leak: '" + v.getName() + "' is allocated by '" +
    alloc.getTarget().getName() +
    "' in function '" + f.getName() +
    "' but this return path does not free it."
