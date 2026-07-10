/**
 * @name Resource leak via early return bypassing cleanup label
 * @description Detects functions that allocate a resource into a local
 *              variable, set up a goto-based cleanup epilogue that releases
 *              it, but contain an early `return` statement that bypasses the
 *              cleanup, leaking the allocated resource.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-lu-2
 */

import cpp

/** Allocation-style call whose return value must be freed via `releaseName`. */
predicate isAllocCall(FunctionCall fc, string releaseName) {
  fc.getTarget().getName() = "kmalloc" and releaseName = "kfree"
  or
  fc.getTarget().getName() = "kzalloc" and releaseName = "kfree"
  or
  fc.getTarget().getName() = "kcalloc" and releaseName = "kfree"
  or
  fc.getTarget().getName() = "kmalloc_array" and releaseName = "kfree"
  or
  fc.getTarget().getName() = "vmalloc" and releaseName = "vfree"
  or
  fc.getTarget().getName() = "vzalloc" and releaseName = "vfree"
  or
  fc.getTarget().getName() = "malloc" and releaseName = "free"
  or
  fc.getTarget().getName() = "calloc" and releaseName = "free"
}

/** The local variable `v` receives the value of allocation call `ac` in `f`. */
predicate allocAssignedTo(Function f, LocalVariable v, FunctionCall ac) {
  ac.getEnclosingFunction() = f and
  (
    exists(AssignExpr ae |
      ae.getRValue() = ac and
      ae.getLValue() = v.getAnAccess()
    )
    or
    v.getInitializer().getExpr() = ac
  )
}

/** A release call on variable `v` in function `f` using `releaseName`. */
predicate releaseOf(Function f, LocalVariable v, string releaseName, FunctionCall rc) {
  rc.getEnclosingFunction() = f and
  rc.getTarget().getName() = releaseName and
  rc.getAnArgument() = v.getAnAccess()
}

/**
 * The return statement is part of the standard allocation-failure null
 * check `if (!v) return ...;` that happens right after the allocation.
 */
predicate isAllocFailureReturn(ReturnStmt ret, LocalVariable v, FunctionCall allocCall) {
  exists(IfStmt ifs |
    ifs.getEnclosingFunction() = ret.getEnclosingFunction() and
    ifs.getCondition().getAChild*() = v.getAnAccess() and
    ifs.getLocation().getStartLine() >= allocCall.getLocation().getStartLine() and
    ifs.getLocation().getStartLine() <= allocCall.getLocation().getStartLine() + 3 and
    ret.getEnclosingStmt*() = ifs.getThen()
  )
}

from
  Function f, LocalVariable v, FunctionCall allocCall, string releaseName,
  ReturnStmt earlyRet, FunctionCall releaseInCleanup, GotoStmt anyGoto
where
  isAllocCall(allocCall, releaseName) and
  allocAssignedTo(f, v, allocCall) and
  releaseOf(f, v, releaseName, releaseInCleanup) and
  // Cleanup is reached via at least one goto in the function (cleanup label
  // pattern).
  anyGoto.getEnclosingFunction() = f and
  anyGoto.getTarget().getLocation().getStartLine() <=
    releaseInCleanup.getLocation().getStartLine() and
  anyGoto.getTarget().getLocation().getStartLine() >
    allocCall.getLocation().getStartLine() and
  // The return occurs after the allocation but before the cleanup release.
  earlyRet.getEnclosingFunction() = f and
  earlyRet.getLocation().getStartLine() > allocCall.getLocation().getStartLine() and
  earlyRet.getLocation().getStartLine() < releaseInCleanup.getLocation().getStartLine() and
  // The return is not the allocation-failure null check.
  not isAllocFailureReturn(earlyRet, v, allocCall) and
  // No release of v occurs between the allocation and this return.
  not exists(FunctionCall freeBefore |
    releaseOf(f, v, releaseName, freeBefore) and
    freeBefore.getLocation().getStartLine() < earlyRet.getLocation().getStartLine() and
    freeBefore.getLocation().getStartLine() > allocCall.getLocation().getStartLine()
  )
select earlyRet,
  "Early return bypasses cleanup label for resource '" + v.getName() +
    "' allocated by '" + allocCall.getTarget().getName() + "' (should '" +
    releaseName + "' before returning, or 'goto' the cleanup label)."
