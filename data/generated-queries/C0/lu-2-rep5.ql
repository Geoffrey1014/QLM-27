/**
 * @name Memory leak via early return bypassing kfree cleanup label
 * @description Detects functions that allocate a buffer (kmalloc/kzalloc/kcalloc/etc.)
 *              and later use a goto-based cleanup label (e.g. `err:`) that calls kfree
 *              on that buffer, but contain a direct `return` statement on an error path
 *              after the allocation succeeds, bypassing the kfree and leaking memory.
 * @kind problem
 * @problem.severity warning
 * @id cpp/early-return-bypass-kfree-cleanup
 * @tags reliability
 *       security
 *       memory-leak
 */

import cpp

/** A call to a kernel allocation function whose return value should be kfree'd. */
class KAllocCall extends FunctionCall {
  KAllocCall() {
    this.getTarget().getName() =
      [
        "kmalloc", "kzalloc", "kcalloc", "kmalloc_array", "kvmalloc", "kvzalloc",
        "kmemdup", "kstrdup", "kstrndup", "krealloc", "vmalloc", "vzalloc"
      ]
  }
}

/** A call to kfree (or its variants) on a given expression. */
class KFreeCall extends FunctionCall {
  KFreeCall() {
    this.getTarget().getName() = ["kfree", "kvfree", "kzfree", "vfree", "kfree_sensitive"]
  }

  Expr getFreedExpr() { result = this.getArgument(0) }
}

/** A local variable that receives the result of a kernel allocation. */
predicate allocatedInto(LocalVariable v, KAllocCall alloc, Function f) {
  f = alloc.getEnclosingFunction() and
  v.getFunction() = f and
  (
    // int *p = kmalloc(...)
    v.getInitializer().getExpr() = alloc
    or
    // p = kmalloc(...)
    exists(AssignExpr ae |
      ae.getEnclosingFunction() = f and
      ae.getLValue() = v.getAnAccess() and
      ae.getRValue() = alloc
    )
  )
}

/** Some statement in `f` frees the variable `v` via kfree. */
predicate freedSomewhere(LocalVariable v, Function f) {
  exists(KFreeCall kf |
    kf.getEnclosingFunction() = f and
    kf.getFreedExpr() = v.getAnAccess()
  )
}

/** A `return` statement that occurs textually after the allocation of `v` in `f`. */
predicate returnAfterAlloc(ReturnStmt ret, LocalVariable v, KAllocCall alloc, Function f) {
  allocatedInto(v, alloc, f) and
  ret.getEnclosingFunction() = f and
  (
    ret.getLocation().getStartLine() > alloc.getLocation().getStartLine()
    or
    ret.getLocation().getStartLine() = alloc.getLocation().getStartLine() and
    ret.getLocation().getStartColumn() > alloc.getLocation().getStartColumn()
  )
}

/**
 * The return statement does NOT itself free the variable, and is not preceded
 * (in the same basic block / immediate predecessor) by a kfree of v.
 */
predicate returnLeaksVar(ReturnStmt ret, LocalVariable v) {
  exists(BasicBlock bb |
    ret.getBasicBlock() = bb and
    not exists(KFreeCall kf |
      kf.getFreedExpr() = v.getAnAccess() and
      kf.getBasicBlock() = bb and
      kf.getLocation().getStartLine() <= ret.getLocation().getStartLine()
    )
  )
}

from
  Function f, LocalVariable v, KAllocCall alloc, ReturnStmt ret
where
  allocatedInto(v, alloc, f) and
  freedSomewhere(v, f) and
  returnAfterAlloc(ret, v, alloc, f) and
  returnLeaksVar(ret, v) and
  // The return must be an error path (returns a non-zero / negative value or an
  // error-like expression), not a normal success exit.
  (
    exists(int k | ret.getExpr().getValue().toInt() = k and k != 0)
    or
    ret.getExpr() instanceof UnaryMinusExpr
    or
    exists(MacroInvocation mi |
      mi.getStmt() = ret or
      mi.getExpr() = ret.getExpr()
    )
  )
select ret,
  "Possible memory leak: this return on an error path bypasses the kfree of '" + v.getName() +
    "' allocated at $@.", alloc, alloc.toString()
