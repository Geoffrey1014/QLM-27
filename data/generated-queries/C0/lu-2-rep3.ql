/**
 * @name Early return bypasses kfree cleanup label causing memory leak
 * @description A function allocates memory with kmalloc/kzalloc/kmemdup and uses a goto-based
 *              cleanup label (e.g. `err:` with kfree) for error handling. Some error paths
 *              return directly with an error code without jumping to the cleanup label,
 *              leaking the allocated buffer. Pattern as fixed in af9005_identify_state
 *              (commit 2289adbfa559).
 * @kind problem
 * @problem.severity warning
 * @id cpp/early-return-leaks-cleanup-buffer
 * @tags correctness
 *       security
 *       memory-leak
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph

/** A call to a kernel allocation routine that returns a pointer the caller must kfree. */
class KernelAllocCall extends FunctionCall {
  KernelAllocCall() {
    this.getTarget().getName() =
      [
        "kmalloc", "kzalloc", "kcalloc", "kmalloc_array", "kmemdup", "kstrdup",
        "kstrndup", "vmalloc", "vzalloc", "kvmalloc", "kvzalloc", "kmalloc_node",
        "kzalloc_node", "kvmalloc_node", "krealloc"
      ]
  }
}

/** A call to a kernel free routine matching the alloc family above. */
class KernelFreeCall extends FunctionCall {
  KernelFreeCall() {
    this.getTarget().getName() = ["kfree", "vfree", "kvfree", "kzfree", "kfree_sensitive"]
  }
}

/**
 * A local variable that is assigned the result of a kernel allocation and is
 * freed via a cleanup label later in the same function.
 */
predicate allocatedAndCleanedUp(Function f, Variable v, KernelAllocCall alloc, KernelFreeCall free) {
  f = alloc.getEnclosingFunction() and
  f = free.getEnclosingFunction() and
  v.getAnAssignedValue() = alloc and
  free.getAnArgument() = v.getAnAccess() and
  // The free is reached via a cleanup label (typical kernel pattern: `err:` / `out:` / `free:`)
  exists(LabelStmt lbl |
    lbl.getEnclosingFunction() = f and
    lbl.getName().regexpMatch("(?i)(err|out|free|fail|cleanup|exit|done|finish).*") and
    // free is lexically at or after the label
    lbl.getLocation().getStartLine() <= free.getLocation().getStartLine()
  )
}

/**
 * A return statement that returns a non-zero (error) constant directly,
 * bypassing the cleanup label.
 */
class ErrorReturn extends ReturnStmt {
  ErrorReturn() {
    exists(Expr e | e = this.getExpr() |
      // negative integer literal: -EIO, -ENOMEM etc. (after macro expansion these are
      // negative literals). Also a unary minus around a literal.
      e.getValue().toInt() < 0
      or
      exists(UnaryMinusExpr um | um = e and um.getOperand() instanceof Literal)
      or
      // identifier-like macros (best effort): the expression's value is a non-zero int constant
      (e.isConstant() and e.getValue().toInt() != 0)
    )
  }
}

/**
 * Holds if the return statement does NOT goto/jump to a label that reaches the free.
 * Heuristic: a direct `return -ERR;` statement which is textually before the cleanup
 * label is suspicious if a buffer is live at that point.
 */
predicate returnBypassesCleanup(Function f, ErrorReturn ret, KernelFreeCall free) {
  ret.getEnclosingFunction() = f and
  free.getEnclosingFunction() = f and
  // Free occurs lexically after the return (i.e. via cleanup label below)
  ret.getLocation().getEndLine() < free.getLocation().getStartLine()
}

from Function f, Variable v, KernelAllocCall alloc, KernelFreeCall free, ErrorReturn ret
where
  allocatedAndCleanedUp(f, v, alloc, free) and
  returnBypassesCleanup(f, ret, free) and
  // The allocation is before the return (the buffer is live at the return point)
  alloc.getLocation().getEndLine() < ret.getLocation().getStartLine() and
  // Exclude returns that themselves return the allocated pointer
  not ret.getExpr().(VariableAccess).getTarget() = v and
  // Exclude returns of 0 / success
  not ret.getExpr().getValue() = "0"
select ret,
  "Early return with error code may leak buffer $@ allocated by $@; cleanup label and $@ are bypassed.",
  v, v.getName(), alloc, alloc.getTarget().getName(), free, "kfree"
