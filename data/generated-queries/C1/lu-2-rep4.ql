/**
 * @name Resource leak: early return bypasses cleanup label
 * @description A function allocates a resource into a local variable and then,
 *              on a later control-flow path, executes a direct `return` that
 *              skips a cleanup label (typically `err:`) that frees the
 *              resource. Modeled after CVE-style memory leaks where the buggy
 *              code uses `return -EIO;` where it should `goto err;`.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-lu-2
 */

import cpp
import semmle.code.cpp.controlflow.Guards

/** A call that allocates a resource and yields a pointer that must be freed. */
predicate isAllocCall(FunctionCall fc) {
  fc.getTarget().getName().regexpMatch("(?i)k[mz]alloc|kmalloc_array|kcalloc|kmemdup|vmalloc|kstrdup|kasprintf")
}

/** A call that releases a resource. */
predicate isFreeCall(FunctionCall fc) {
  fc.getTarget().getName().regexpMatch("(?i)kfree|vfree|kvfree|kzfree")
}

/** A label-statement whose target serves as a function's cleanup epilogue. */
predicate isCleanupLabel(LabelStmt ls) {
  ls.getName().regexpMatch("(?i).*(err|fail|out|cleanup|free|exit|undo|release).*")
}

/**
 * Holds if `f` contains an allocation assigned to a local variable `v`,
 * a cleanup label whose body frees `v`, and a direct `return` that
 * lexically follows the allocation but lies *before* the cleanup label
 * and is not preceded on its path by any free of `v`.
 *
 * This captures the buggy `return -EIO;` that bypasses the `err:` label.
 */
from Function f, FunctionCall alloc, LocalVariable v, ReturnStmt ret,
     LabelStmt cleanup, FunctionCall free
where
  // allocation in f, result flows into local variable v
  isAllocCall(alloc) and
  alloc.getEnclosingFunction() = f and
  exists(AssignExpr ae |
    ae.getRValue() = alloc and
    ae.getLValue() = v.getAnAccess()
  ) and
  // function has a cleanup label that frees v
  cleanup.getEnclosingFunction() = f and
  isCleanupLabel(cleanup) and
  isFreeCall(free) and
  free.getEnclosingFunction() = f and
  free.getAnArgument() = v.getAnAccess() and
  // the free call is dominated by / inside the cleanup label region:
  // it comes (lexically) at or after the label.
  free.getLocation().getStartLine() >= cleanup.getLocation().getStartLine() and
  // the suspect early return:
  ret.getEnclosingFunction() = f and
  // return lies between the allocation and the cleanup label
  ret.getLocation().getStartLine() > alloc.getLocation().getStartLine() and
  ret.getLocation().getStartLine() < cleanup.getLocation().getStartLine() and
  // and the return is not itself a free-then-return: no free of v before
  // this return on its control-flow path within the function.
  not exists(FunctionCall otherFree |
    isFreeCall(otherFree) and
    otherFree.getEnclosingFunction() = f and
    otherFree.getAnArgument() = v.getAnAccess() and
    otherFree.getLocation().getStartLine() < ret.getLocation().getStartLine() and
    otherFree.getLocation().getStartLine() > alloc.getLocation().getStartLine()
  ) and
  // and the return does NOT immediately follow the allocation-failure check
  // (i.e., not the `if (!v) return -ENOMEM;` pattern). Heuristic: there
  // must be at least one statement between the allocation and the return
  // beyond the null-check.
  ret.getLocation().getStartLine() - alloc.getLocation().getStartLine() >= 3
select ret,
  "Early return at line " + ret.getLocation().getStartLine().toString() +
  " bypasses cleanup label '" + cleanup.getName() +
  "' that frees '" + v.getName() + "' (allocated at line " +
  alloc.getLocation().getStartLine().toString() + ")."
