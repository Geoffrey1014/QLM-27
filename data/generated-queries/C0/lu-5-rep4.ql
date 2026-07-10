/**
 * @name Missing kfree on some return paths for kstrdup-allocated buffer
 * @description A local pointer is assigned the result of kstrdup/kmemdup/kstrndup
 *              (or similar allocators) and is freed on at least one return path
 *              from the enclosing function but not on all return paths, indicating
 *              a likely memory leak (as in affs_remount where new_opts was only
 *              freed on the parse_options failure path).
 * @kind problem
 * @problem.severity warning
 * @id cpp/missing-kfree-some-paths
 * @tags correctness
 *       memory-leak
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph

/** A call that allocates a buffer that the caller owns and must kfree. */
class AllocCall extends FunctionCall {
  AllocCall() {
    this.getTarget().getName() =
      [
        "kstrdup", "kstrdup_const", "kstrndup",
        "kmemdup", "kmemdup_nul",
        "kasprintf", "kvasprintf",
        "kzalloc", "kmalloc", "kcalloc", "kvmalloc", "kvzalloc"
      ]
  }
}

/** A call to a kfree-family release on `e`. */
predicate isFreeOf(FunctionCall fc, Expr e) {
  fc.getTarget().getName() in [
      "kfree", "kvfree", "kzfree", "kfree_sensitive", "kfree_const"
    ] and
  fc.getArgument(0) = e
}

/** Holds if `v` is freed somewhere inside function `f`. */
predicate variableFreedInFunction(LocalVariable v, Function f) {
  exists(FunctionCall fc, VariableAccess va |
    fc.getEnclosingFunction() = f and
    va.getTarget() = v and
    isFreeOf(fc, va)
  )
}

/**
 * Holds if `ret` is a ReturnStmt in `f` such that no kfree(v) executes on the
 * path reaching `ret` after the allocation `alloc` to `v`.
 *
 * Approximation: we look for a return statement that is control-flow reachable
 * from `alloc`, and for which no kfree-of-`v` call lies on a path between
 * `alloc` and `ret`.
 */
predicate returnWithoutFree(LocalVariable v, AllocCall alloc, ReturnStmt ret) {
  exists(Function f |
    alloc.getEnclosingFunction() = f and
    ret.getEnclosingFunction() = f and
    // alloc is reassigned to v (v = alloc(...))
    exists(Expr assignedTo |
      (
        // initializer: T *v = alloc(...)
        v.getInitializer().getExpr() = alloc and assignedTo = alloc
      )
      or
      exists(AssignExpr ae |
        ae.getRValue() = alloc and
        ae.getLValue().(VariableAccess).getTarget() = v and
        assignedTo = ae
      )
    ) and
    // ret is reachable from alloc via successor edges
    alloc.getASuccessor+() = ret and
    // No kfree(v) appears on any path between alloc and ret
    not exists(FunctionCall fc, VariableAccess va |
      fc.getEnclosingFunction() = f and
      isFreeOf(fc, va) and
      va.getTarget() = v and
      alloc.getASuccessor+() = fc and
      fc.getASuccessor+() = ret
    )
  )
}

from LocalVariable v, AllocCall alloc, ReturnStmt leakRet, Function f
where
  f = alloc.getEnclosingFunction() and
  returnWithoutFree(v, alloc, leakRet) and
  // require evidence the variable IS freed on at least one other path — this is
  // the "fix existed on the error path, not on success" shape from the seed
  variableFreedInFunction(v, f) and
  // exclude returns of the allocated pointer itself (ownership transferred)
  not leakRet.getExpr().(VariableAccess).getTarget() = v
select leakRet,
  "Variable '$@' allocated by '$@' at $@ may not be kfree'd on this return path " +
    "(it is freed on some other path in the same function, suggesting a missing kfree here).",
  v, v.getName(), alloc.getTarget(), alloc.getTarget().getName(), alloc, alloc.toString()
