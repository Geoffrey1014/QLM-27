/**
 * @name Direct return bypasses cleanup label after allocation
 * @description A function allocates a resource (e.g. via kmalloc/kzalloc/kcalloc) and
 *              installs a cleanup label (typically `err:`/`out:`/`fail:`) that other
 *              error paths jump to via `goto`. A `return` statement that exits the
 *              function without going through the cleanup label after the allocation
 *              has succeeded leaks the resource.
 * @kind problem
 * @problem.severity warning
 * @id cpp/return-bypasses-cleanup-label
 * @tags correctness
 *       reliability
 *       memory-leak
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph

/** A call to a kernel allocation function whose returned pointer must be released. */
class AllocCall extends FunctionCall {
  AllocCall() {
    this.getTarget().getName() =
      ["kmalloc", "kzalloc", "kcalloc", "kmalloc_array", "kmemdup", "kstrdup",
       "kstrndup", "vmalloc", "vzalloc", "kvmalloc", "kvzalloc",
       "devm_kmalloc", "krealloc"]
  }
}

/** A label that looks like an error/cleanup landing-pad. */
class CleanupLabel extends LabelStmt {
  CleanupLabel() {
    exists(string n | n = this.getName().toLowerCase() |
      n.matches("err%") or
      n.matches("out%") or
      n.matches("fail%") or
      n.matches("free%") or
      n.matches("cleanup%") or
      n = "exit" or
      n.matches("unlock%") or
      n.matches("release%")
    )
  }
}

/** A `goto` statement that targets a cleanup-style label. */
class CleanupGoto extends GotoStmt {
  CleanupGoto() { this.getTarget() instanceof CleanupLabel }
}

/**
 * Holds if `f` has the shape:
 *   - some allocation call `alloc`,
 *   - a cleanup label `lbl` reachable from `alloc`,
 *   - at least one `goto lbl` in `f` (so the label is the established error path).
 */
predicate hasCleanupPattern(Function f, AllocCall alloc, CleanupLabel lbl) {
  alloc.getEnclosingFunction() = f and
  lbl.getEnclosingFunction() = f and
  exists(CleanupGoto g |
    g.getEnclosingFunction() = f and g.getTarget() = lbl
  )
}

/**
 * Holds if `ret` is a `return` statement that is reachable from `alloc` along the CFG
 * and does NOT pass through `lbl` first. That is, the return exits the function
 * after the allocation succeeded without performing cleanup.
 */
predicate returnBypassesLabel(ReturnStmt ret, AllocCall alloc, CleanupLabel lbl) {
  ret.getEnclosingFunction() = alloc.getEnclosingFunction() and
  ret.getEnclosingFunction() = lbl.getEnclosingFunction() and
  // ret is control-flow reachable from after the allocation
  alloc.getASuccessor+() = ret and
  // the cleanup label is NOT on the path from alloc to ret
  not exists(ControlFlowNode mid |
    alloc.getASuccessor+() = mid and
    mid.getASuccessor+() = ret and
    mid = lbl
  ) and
  // exclude the case where the return IS the cleanup-label tail
  not lbl.getASuccessor*() = ret
}

from Function f, AllocCall alloc, CleanupLabel lbl, ReturnStmt ret
where
  hasCleanupPattern(f, alloc, lbl) and
  returnBypassesLabel(ret, alloc, lbl) and
  // suppress trivial "return 0" tails by requiring the return to occur strictly
  // before the cleanup label textually too (most real bugs are early returns
  // in the middle of the function)
  ret.getLocation().getStartLine() < lbl.getLocation().getStartLine()
select ret,
  "This return on line " + ret.getLocation().getStartLine() +
    " bypasses the cleanup label '" + lbl.getName() + "' (line " +
    lbl.getLocation().getStartLine() +
    "), leaking the resource allocated at line " +
    alloc.getLocation().getStartLine() + "."
