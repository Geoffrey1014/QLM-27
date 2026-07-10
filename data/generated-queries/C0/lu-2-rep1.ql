/**
 * @name Early return after allocation without freeing in error path
 * @description Detects functions that allocate a buffer (e.g. via kmalloc/kzalloc/kmemdup)
 *              then return an error code on some path without going through the unified
 *              cleanup label that calls kfree on the buffer. Pattern abstracted from the
 *              af9005_identify_state memory leak fix where `return -EIO` skipped a kfree
 *              that the err: label performs.
 * @kind problem
 * @problem.severity warning
 * @id cpp/early-return-leaks-alloc
 * @tags reliability
 *       security
 *       memory-leak
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph

/** A function call that allocates kernel memory and returns the pointer. */
class KernelAllocCall extends FunctionCall {
  KernelAllocCall() {
    this.getTarget().getName() =
      [
        "kmalloc", "kzalloc", "kcalloc", "kmemdup", "kstrdup", "kstrndup",
        "vmalloc", "vzalloc", "kvmalloc", "kvzalloc",
        "kmalloc_array", "kvmalloc_array", "krealloc", "devm_kzalloc",
        "kmalloc_node", "kzalloc_node"
      ]
  }
}

/** A free call on the given expression. */
predicate isFreeOf(FunctionCall fc, Expr v) {
  fc.getTarget().getName() = ["kfree", "kvfree", "vfree", "kzfree", "kfree_sensitive"] and
  fc.getArgument(0).(VariableAccess).getTarget() = v.(VariableAccess).getTarget()
}

/** A return statement that yields a non-zero (error) constant. */
class ErrorReturnStmt extends ReturnStmt {
  ErrorReturnStmt() {
    exists(Expr e | e = this.getExpr() |
      // negative integer constant like -EIO, -ENOMEM, ...
      e.getValue().toInt() < 0
      or
      // -SOMETHING via unary minus
      e instanceof UnaryMinusExpr
      or
      // ERR_PTR(...) returned (less common for int returns but tolerated)
      e.(FunctionCall).getTarget().getName() = "ERR_PTR"
    )
  }
}

/**
 * Holds if `f` has a unified cleanup label (any labeled stmt) which is reached
 * by some path containing a kfree of the allocated pointer.
 */
predicate hasCleanupFreeing(Function f, Variable buf) {
  exists(FunctionCall free |
    free.getEnclosingFunction() = f and
    free.getTarget().getName() = ["kfree", "kvfree", "vfree", "kzfree", "kfree_sensitive"] and
    free.getArgument(0).(VariableAccess).getTarget() = buf
  )
}

/**
 * Holds if the return statement `ret` is dominated (in source order within the
 * function) by an allocation into `buf`, and there is NO kfree of `buf` on the
 * straight-line path from the alloc to this return (i.e. the return bypasses
 * the cleanup).
 */
predicate earlyReturnSkipsFree(Function f, Variable buf, KernelAllocCall alloc, ErrorReturnStmt ret) {
  alloc.getEnclosingFunction() = f and
  ret.getEnclosingFunction() = f and
  // alloc result is assigned to buf
  exists(AssignExpr a |
    a.getLValue().(VariableAccess).getTarget() = buf and
    a.getRValue() = alloc
  )
  and
  // return appears after the alloc in source order
  ret.getLocation().getStartLine() > alloc.getLocation().getStartLine() and
  // function does contain a cleanup kfree(buf) somewhere
  hasCleanupFreeing(f, buf) and
  // but no kfree(buf) lies textually between the alloc and this return
  not exists(FunctionCall free |
    free.getEnclosingFunction() = f and
    free.getTarget().getName() = ["kfree", "kvfree", "vfree", "kzfree", "kfree_sensitive"] and
    free.getArgument(0).(VariableAccess).getTarget() = buf and
    free.getLocation().getStartLine() > alloc.getLocation().getStartLine() and
    free.getLocation().getStartLine() < ret.getLocation().getStartLine()
  )
  and
  // and no `goto <label>` between alloc and return that would route to cleanup
  not exists(GotoStmt g |
    g.getEnclosingFunction() = f and
    g.getLocation().getStartLine() > alloc.getLocation().getStartLine() and
    g.getLocation().getStartLine() < ret.getLocation().getStartLine()
  )
}

from Function f, Variable buf, KernelAllocCall alloc, ErrorReturnStmt ret
where earlyReturnSkipsFree(f, buf, alloc, ret)
select ret,
  "Early error return in '" + f.getName() +
    "' may leak buffer '" + buf.getName() +
    "' allocated at $@ — cleanup path (kfree) is bypassed.",
  alloc, alloc.getTarget().getName()
