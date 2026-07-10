/**
 * @name  rq3-c2-lu-2-rep2
 * @id    cpp/rq3/c2/lu-2-rep2
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *   Detects a function that allocates a resource (e.g. kmalloc), has a
 *   cleanup label that frees it, but contains an early return statement
 *   that bypasses the cleanup, leaking the resource.
 */

import cpp

/** Holds if `fc` is a call to a kernel allocation function returning a pointer. */
predicate isAllocCall(FunctionCall fc) {
  fc.getTarget().getName() = ["kmalloc", "kzalloc", "kcalloc", "kmemdup",
                              "vmalloc", "vzalloc", "kstrdup", "kmalloc_array"]
}

/** Holds if `fc` is a call that releases an allocated buffer. */
predicate isFreeCall(FunctionCall fc) {
  fc.getTarget().getName() = ["kfree", "vfree", "kvfree"]
}

/**
 * Holds if local variable `v` in function `f` is assigned the result of an
 * allocation call.
 */
predicate allocatedLocal(Function f, LocalVariable v) {
  v.getFunction() = f and
  exists(FunctionCall fc |
    isAllocCall(fc) and
    (
      v.getInitializer().getExpr() = fc
      or
      exists(AssignExpr ae |
        ae.getEnclosingFunction() = f and
        ae.getLValue().(VariableAccess).getTarget() = v and
        ae.getRValue() = fc
      )
    )
  )
}

/**
 * Holds if function `f` has a cleanup label `lbl` whose subsequent statements
 * include a free of variable `v`.
 */
predicate hasCleanupLabelFor(Function f, LabelStmt lbl, LocalVariable v) {
  lbl.getEnclosingFunction() = f and
  exists(FunctionCall fc |
    isFreeCall(fc) and
    fc.getEnclosingFunction() = f and
    fc.getArgument(0).(VariableAccess).getTarget() = v and
    // free occurs at/after the cleanup label
    fc.getLocation().getStartLine() >= lbl.getLocation().getStartLine()
  )
}

/**
 * Holds if `ret` is a return statement in `f` that bypasses cleanup label
 * `lbl`: it returns directly without doing `goto lbl` and is located before
 * the label.
 */
predicate bypassesCleanup(Function f, ReturnStmt ret, LabelStmt lbl) {
  ret.getEnclosingFunction() = f and
  lbl.getEnclosingFunction() = f and
  ret.getLocation().getStartLine() < lbl.getLocation().getStartLine() and
  // not preceded immediately by a goto to lbl - simpler: this return is the
  // path itself.
  exists(ret.getExpr())
}

from Function f, LocalVariable v, LabelStmt lbl, ReturnStmt ret
where
  allocatedLocal(f, v) and
  hasCleanupLabelFor(f, lbl, v) and
  bypassesCleanup(f, ret, lbl)
select ret,
  "Possible resource leak: return bypasses cleanup label '" + lbl.getName() +
  "' which frees '" + v.getName() + "'."
