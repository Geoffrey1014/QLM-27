/**
 * @name Possible memory leak of kstrdup/kmemdup result
 * @description A pointer returned by an allocating duplicator (kstrdup,
 *              kstrdup_const, kmemdup, kasprintf, kvasprintf) is assigned to a
 *              local variable, but at least one reachable return from the
 *              function does not free that variable via kfree/kvfree/kfree_const.
 *              This generalises the affs_remount leak fixed in commit
 *              450c3d416683 ("affs: fix a memory leak in affs_remount").
 * @kind problem
 * @problem.severity warning
 * @id cpp/kernel-kstrdup-leak
 * @tags correctness
 *       memory-leak
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph

/** A kernel function that returns a freshly allocated heap pointer the caller owns. */
class AllocDuplicator extends Function {
  AllocDuplicator() {
    this.getName() in [
        "kstrdup", "kstrdup_const",
        "kmemdup", "kmemdup_nul",
        "kasprintf", "kvasprintf",
        "kvasprintf_const"
      ]
  }
}

/** A kernel deallocator that releases such a pointer. */
class Deallocator extends Function {
  Deallocator() {
    this.getName() in [
        "kfree", "kfree_const", "kvfree", "kzfree",
        "kfree_sensitive", "kvfree_sensitive"
      ]
  }
}

/** A call to an allocating duplicator whose result is stored in a local variable. */
predicate allocAssignedToLocal(FunctionCall alloc, LocalVariable v, Function enclosing) {
  alloc.getTarget() instanceof AllocDuplicator and
  enclosing = alloc.getEnclosingFunction() and
  exists(AssignExpr ae |
    ae.getRValue() = alloc and
    ae.getLValue() = v.getAnAccess()
  )
  or
  alloc.getTarget() instanceof AllocDuplicator and
  enclosing = alloc.getEnclosingFunction() and
  v.getInitializer().getExpr() = alloc
}

/** Some statement in `f` frees `v` (passes it to a deallocator). */
predicate freesVariable(Function f, LocalVariable v) {
  exists(FunctionCall fc |
    fc.getEnclosingFunction() = f and
    fc.getTarget() instanceof Deallocator and
    fc.getAnArgument() = v.getAnAccess()
  )
}

/** `v` is passed to some other (non-dealloc) function — assume it may transfer ownership. */
predicate escapes(Function f, LocalVariable v) {
  exists(FunctionCall fc |
    fc.getEnclosingFunction() = f and
    not fc.getTarget() instanceof Deallocator and
    not fc.getTarget() instanceof AllocDuplicator and
    fc.getAnArgument() = v.getAnAccess()
  )
  or
  // Returned directly to caller.
  exists(ReturnStmt rs |
    rs.getEnclosingFunction() = f and
    rs.getExpr() = v.getAnAccess()
  )
  or
  // Stored into a field / global / pointer dereference.
  exists(AssignExpr ae |
    ae.getEnclosingFunction() = f and
    ae.getRValue() = v.getAnAccess() and
    not ae.getLValue() instanceof VariableAccess
  )
}

/**
 * Holds if `ret` is a return statement reachable from `alloc` along the CFG
 * with no kfree of `v` in between.
 */
predicate returnWithoutFree(FunctionCall alloc, LocalVariable v, ReturnStmt ret) {
  ret.getEnclosingFunction() = alloc.getEnclosingFunction() and
  exists(ControlFlowNode n |
    n = ret and
    alloc.getASuccessor+() = n
  ) and
  not exists(FunctionCall freeCall |
    freeCall.getEnclosingFunction() = alloc.getEnclosingFunction() and
    freeCall.getTarget() instanceof Deallocator and
    freeCall.getAnArgument() = v.getAnAccess() and
    alloc.getASuccessor+() = freeCall and
    freeCall.getASuccessor+() = ret
  )
}

from FunctionCall alloc, LocalVariable v, Function f, ReturnStmt ret
where
  allocAssignedToLocal(alloc, v, f) and
  freesVariable(f, v) and
  not escapes(f, v) and
  returnWithoutFree(alloc, v, ret) and
  // Avoid noise on tiny accessor wrappers (must have at least one kfree somewhere — already enforced).
  alloc.getFile().getRelativePath().matches("%.c")
select alloc,
  "Result of " + alloc.getTarget().getName() +
    "() stored in '" + v.getName() +
    "' may leak: a return at $@ is reachable without an intervening kfree.",
  ret, "this return"
