/**
 * @name Potential memory leak of kstrdup/kmemdup allocation on some return paths
 * @description A pointer obtained from kstrdup/kmemdup/kstrndup is stored in a local variable
 *              and on at least one return path from the enclosing function, the variable is
 *              neither freed (kfree/kvfree/kfree_sensitive) nor escaped (stored into a field,
 *              passed to another function, or returned). This matches the affs_remount-style
 *              leak fixed by commit 450c3d416683 where new_opts = kstrdup(data, GFP_KERNEL)
 *              leaked on the EINVAL/parse-failure path.
 * @kind problem
 * @problem.severity warning
 * @id cpp/kstrdup-leak-on-return-path
 * @tags reliability
 *       security
 *       external/cwe/cwe-401
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph

/** kstrdup/kmemdup/kstrndup family — allocate memory the caller must free. */
class KAllocDupCall extends FunctionCall {
  KAllocDupCall() {
    this.getTarget().getName() =
      ["kstrdup", "kstrdup_const", "kmemdup", "kmemdup_nul", "kstrndup", "kasprintf", "kvasprintf"]
  }
}

/** kfree-family deallocators. */
predicate isFreeCall(FunctionCall fc, Expr arg) {
  fc.getTarget().getName() = ["kfree", "kvfree", "kfree_sensitive", "kzfree", "kfree_const"] and
  arg = fc.getArgument(0)
}

/** A local variable assigned the result of a kstrdup-style allocation. */
predicate allocAssignedToLocal(KAllocDupCall alloc, LocalVariable v, Function f) {
  f = alloc.getEnclosingFunction() and
  v.getFunction() = f and
  exists(AssignExpr ae |
    ae.getRValue() = alloc and
    ae.getLValue() = v.getAnAccess()
  )
  or
  f = alloc.getEnclosingFunction() and
  v.getFunction() = f and
  v.getInitializer().getExpr() = alloc
}

/** True if `e` reads variable `v`. */
predicate readsVar(Expr e, LocalVariable v) { e = v.getAnAccess() }

/**
 * True if execution reaching `ret` could have come from `alloc` without `v` being
 * either freed or "escaped" (passed to a callee, stored into a field, or returned).
 */
predicate leakedAtReturn(KAllocDupCall alloc, LocalVariable v, ReturnStmt ret) {
  exists(Function f |
    allocAssignedToLocal(alloc, v, f) and
    ret.getEnclosingFunction() = f
  ) and
  // The return is reachable from the allocation point in the CFG.
  alloc.getASuccessor+() = ret and
  // No free of v on the path from alloc to ret.
  not exists(FunctionCall freec, Expr a |
    isFreeCall(freec, a) and
    readsVar(a, v) and
    freec.getEnclosingFunction() = ret.getEnclosingFunction() and
    alloc.getASuccessor+() = freec and
    freec.getASuccessor+() = ret
  ) and
  // No escape: v not passed to any other function call on the path.
  not exists(FunctionCall escape, int i |
    escape.getEnclosingFunction() = ret.getEnclosingFunction() and
    readsVar(escape.getArgument(i), v) and
    alloc.getASuccessor+() = escape and
    escape.getASuccessor+() = ret and
    not isFreeCall(escape, escape.getArgument(i))
  ) and
  // v is not returned.
  not readsVar(ret.getExpr(), v) and
  // v is not stored into a field or other lvalue.
  not exists(AssignExpr store |
    store.getRValue() = v.getAnAccess() and
    store.getEnclosingFunction() = ret.getEnclosingFunction() and
    not store.getLValue() = v.getAnAccess() and
    alloc.getASuccessor+() = store and
    store.getASuccessor+() = ret
  )
}

from KAllocDupCall alloc, LocalVariable v, ReturnStmt ret
where
  leakedAtReturn(alloc, v, ret) and
  // Restrict to cases where there IS at least one free of v somewhere in the
  // function — this filters out functions that intentionally hand ownership
  // to a caller and dramatically reduces false positives.
  exists(FunctionCall freec, Expr a |
    isFreeCall(freec, a) and
    readsVar(a, v) and
    freec.getEnclosingFunction() = ret.getEnclosingFunction()
  )
select ret,
  "Possible memory leak: variable $@ holds allocation from $@ but is not freed on this return path.",
  v, v.getName(), alloc, alloc.getTarget().getName()
