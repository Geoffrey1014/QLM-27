/**
 * @name Missing kfree on kstrdup-allocated buffer on some return paths
 * @description Detects functions that allocate a buffer via kstrdup/kmemdup/kasprintf
 *              (or similar k*dup/kasprintf allocators) and store it in a local variable,
 *              but fail to release the buffer on at least one return path. This is the
 *              pattern fixed by commit 450c3d416683 ("affs: fix a memory leak in
 *              affs_remount"), where new_opts was freed only on the parse_options error
 *              path but leaked on the success path.
 * @kind problem
 * @problem.severity warning
 * @id cpp/kstrdup-missing-kfree-on-some-path
 * @tags correctness
 *       memory-leak
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph

/**
 * Kernel allocators that return heap memory ownership to the caller, where the
 * canonical release function is kfree() (or kvfree/kfree_const). All of them
 * follow the same "acquire->release" lifecycle as kstrdup.
 */
predicate isKstrdupLikeAllocator(Function f) {
  exists(string n | n = f.getName() |
    n = "kstrdup" or
    n = "kstrdup_const" or
    n = "kmemdup" or
    n = "kmemdup_nul" or
    n = "kasprintf" or
    n = "kvasprintf" or
    n = "kstrndup"
  )
}

/** A call to one of the kstrdup-like allocators. */
class KstrdupLikeCall extends FunctionCall {
  KstrdupLikeCall() { isKstrdupLikeAllocator(this.getTarget()) }
}

/**
 * A release function that consumes the buffer (kfree family). Calling any of
 * these on the critical variable is considered a valid post-operation.
 */
predicate isKfreeLike(Function f) {
  exists(string n | n = f.getName() |
    n = "kfree" or
    n = "kvfree" or
    n = "kfree_const" or
    n = "kfree_sensitive" or
    n = "kzfree"
  )
}

/** A call kfree(v) (or kvfree(v), etc.) where v refers to local `lv`. */
predicate releasesLocal(ControlFlowNode cfn, LocalVariable lv) {
  exists(FunctionCall fc, VariableAccess va |
    fc = cfn and
    isKfreeLike(fc.getTarget()) and
    va = fc.getAnArgument().getAChild*() and
    va.getTarget() = lv
  )
  or
  // also count direct argument access
  exists(FunctionCall fc, VariableAccess va |
    fc = cfn and
    isKfreeLike(fc.getTarget()) and
    va = fc.getAnArgument() and
    va.getTarget() = lv
  )
}

/**
 * A "leaking" return statement: there exists a return that is reachable from the
 * allocation site without any kfree-like release of the critical variable on
 * the path from the alloc to that return.
 */
predicate leakingReturn(
  KstrdupLikeCall alloc, LocalVariable lv, ReturnStmt ret
) {
  // alloc must store into lv
  exists(Assignment a |
    a.getRValue() = alloc and
    a.getLValue().(VariableAccess).getTarget() = lv
  )
  and
  ret.getEnclosingFunction() = alloc.getEnclosingFunction()
  and
  // path from alloc to ret exists with no kfree-like release of lv along the way
  exists(ControlFlowNode mid |
    mid = ret and
    alloc.getASuccessor+() = mid and
    not exists(ControlFlowNode rel |
      alloc.getASuccessor+() = rel and
      rel.getASuccessor*() = mid and
      releasesLocal(rel, lv)
    )
  )
}

from KstrdupLikeCall alloc, LocalVariable lv, ReturnStmt ret, Function f
where
  f = alloc.getEnclosingFunction() and
  leakingReturn(alloc, lv, ret) and
  // require at least one OTHER return in the same function that DOES release lv,
  // mirroring the affs_remount shape (some paths free, some don't). This kills the
  // never-freed FPs (caller-owned buffers handed off via return).
  exists(ReturnStmt good, ControlFlowNode rel |
    good.getEnclosingFunction() = f and
    good != ret and
    alloc.getASuccessor+() = rel and
    rel.getASuccessor*() = good and
    releasesLocal(rel, lv)
  )
select alloc,
  "Buffer allocated by $@ is stored in '" + lv.getName() +
    "' but is not released on the return at $@; other returns in the same function do free it, suggesting a missing kfree on this path.",
  alloc.getTarget(), alloc.getTarget().getName(),
  ret, "this return"
