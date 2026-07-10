/**
 * @name Memory leak from kstrdup/kmemdup on success path
 * @description A pointer obtained via kstrdup/kstrdup_const/kmemdup/kasprintf must be
 *              released with kfree on every path that leaves the scope. When the
 *              allocation is only freed on an error/failure branch but not on the
 *              successful return path, the memory is leaked. This pattern was the
 *              basis of the affs_remount leak (commit 450c3d416683).
 * @kind problem
 * @problem.severity warning
 * @id cpp/kstrdup-success-path-leak
 * @tags reliability
 *       resource-leak
 *       kernel
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph

/**
 * Kernel allocation helpers whose return value (a heap pointer) must be released
 * with `kfree` (or a thin wrapper such as `kfree_const`) on every exit path.
 */
predicate kallocName(string n) {
  n = "kstrdup" or
  n = "kstrdup_const" or
  n = "kmemdup" or
  n = "kmemdup_nul" or
  n = "kasprintf" or
  n = "kvasprintf"
}

/** A call to one of the kalloc helpers. */
class KAllocCall extends FunctionCall {
  KAllocCall() { kallocName(this.getTarget().getName()) }
}

/** Free-like function names that release a kalloc pointer. */
predicate kfreeName(string n) {
  n = "kfree" or
  n = "kfree_const" or
  n = "kvfree" or
  n = "kzfree" or
  n = "kfree_sensitive"
}

/** A call that frees its first argument. */
class KFreeCall extends FunctionCall {
  KFreeCall() { kfreeName(this.getTarget().getName()) }
  Expr getFreedArg() { result = this.getArgument(0) }
}

/**
 * Holds if `v` is assigned the result of a kalloc call `alloc` inside function
 * `f`. The variable serves as the critical resource holder.
 */
predicate allocAssignedTo(Function f, LocalScopeVariable v, KAllocCall alloc) {
  alloc.getEnclosingFunction() = f and
  (
    // local declared with initializer: char *p = kstrdup(...);
    exists(Initializer init |
      v.getInitializer() = init and init.getExpr() = alloc
    )
    or
    // assignment: p = kstrdup(...);
    exists(AssignExpr a |
      a.getEnclosingFunction() = f and
      a.getLValue() = v.getAnAccess() and
      a.getRValue() = alloc
    )
  )
}

/** Holds if some `kfree`-like call in `f` frees variable `v`. */
predicate freedSomewhere(Function f, LocalScopeVariable v) {
  exists(KFreeCall kf |
    kf.getEnclosingFunction() = f and
    kf.getFreedArg() = v.getAnAccess()
  )
}

/** Holds if `v` is returned from `f` (ownership escapes the function). */
predicate returnedFrom(Function f, LocalScopeVariable v) {
  exists(ReturnStmt rs |
    rs.getEnclosingFunction() = f and
    rs.getExpr() = v.getAnAccess()
  )
}

/** Holds if `v` is stored into a field/global (ownership escapes). */
predicate storedIntoNonLocal(Function f, LocalScopeVariable v) {
  exists(AssignExpr a |
    a.getEnclosingFunction() = f and
    a.getRValue() = v.getAnAccess() and
    (
      a.getLValue() instanceof FieldAccess
      or
      exists(VariableAccess va | va = a.getLValue() and not va.getTarget() instanceof LocalScopeVariable)
      or
      a.getLValue() instanceof PointerDereferenceExpr
    )
  )
}

/** Holds if `v` is passed as an argument to any non-free call (potential ownership transfer). */
predicate passedToOtherCall(Function f, LocalScopeVariable v) {
  exists(FunctionCall c |
    c.getEnclosingFunction() = f and
    not c instanceof KFreeCall and
    not c instanceof KAllocCall and
    c.getAnArgument() = v.getAnAccess()
  )
}

/**
 * Number of return statements in `f` whose control-flow predecessor chain does
 * NOT pass through any kfree-of-v call. Approximate: count returns that do not
 * have a kfree(v) dominating them. We approximate with a syntactic check:
 * the function has at least one return statement and at least one return is
 * NOT immediately preceded by a kfree(v).
 */
predicate hasReturnWithoutFree(Function f, LocalScopeVariable v, ReturnStmt rs) {
  rs.getEnclosingFunction() = f and
  not exists(KFreeCall kf |
    kf.getEnclosingFunction() = f and
    kf.getFreedArg() = v.getAnAccess() and
    // kf precedes rs in CFG
    kf.getASuccessor*() = rs
  )
}

from Function f, LocalScopeVariable v, KAllocCall alloc, ReturnStmt rs
where
  allocAssignedTo(f, v, alloc) and
  // there must be SOME kfree of v in the function (otherwise it's a totally-unfreed
  // leak which is a different and noisier pattern; here we focus on the
  // partial-free case the affs_remount commit demonstrates).
  freedSomewhere(f, v) and
  // ownership does not obviously escape
  not returnedFrom(f, v) and
  not storedIntoNonLocal(f, v) and
  not passedToOtherCall(f, v) and
  // at least one return path is reachable without a preceding kfree(v)
  hasReturnWithoutFree(f, v, rs) and
  // exclude trivial cases where the function has only one return and it is the
  // one that frees (avoid double-counting): require at least one kfree exists
  // but does not dominate `rs`
  exists(KFreeCall kf |
    kf.getEnclosingFunction() = f and
    kf.getFreedArg() = v.getAnAccess()
  )
select alloc,
  "Memory allocated by $@ assigned to '" + v.getName() +
    "' may leak: return at $@ has no preceding kfree of '" + v.getName() + "' (partial-free pattern).",
  alloc.getTarget(), alloc.getTarget().getName(),
  rs, "this return"
