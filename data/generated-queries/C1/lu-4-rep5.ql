/**
 * @name Resource leak: early return on error skips later release call (lu-4)
 * @description A pointer is assigned the result of an acquisition-style
 *              call (e.g. *_alloc()). The enclosing function later
 *              releases that pointer with a matching call (e.g. *_put()).
 *              An error-conditional return between the acquisition and
 *              the release skips the release on that path, leaking the
 *              acquired resource.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-lu-4
 * @tags reliability correctness
 */

import cpp

bindingset[n]
predicate isAcquireName(string n) {
  n.matches("%_alloc") or
  n.matches("%alloc_%") or
  n.matches("alloc_%") or
  n.matches("kmalloc%") or
  n.matches("kzalloc") or
  n.matches("kcalloc") or
  n.matches("%_create") or
  n.matches("%_get") or
  n.matches("%_get_%")
}

bindingset[n]
predicate isReleaseName(string n) {
  n.matches("%_put") or
  n.matches("%_put_%") or
  n.matches("%_free") or
  n.matches("free_%") or
  n.matches("kfree") or
  n.matches("kfree_%") or
  n.matches("%_release") or
  n.matches("%_destroy") or
  n.matches("%_unref")
}

/** Two expressions name the same storage: same local variable OR same
 *  field of the same local variable. */
predicate sameStorage(Expr a, Expr b) {
  exists(LocalVariable v |
    a = v.getAnAccess() and b = v.getAnAccess()
  )
  or
  exists(Field fld, LocalVariable v |
    a.(FieldAccess).getTarget() = fld and
    b.(FieldAccess).getTarget() = fld and
    a.(FieldAccess).getQualifier().(VariableAccess).getTarget() = v and
    b.(FieldAccess).getQualifier().(VariableAccess).getTarget() = v
  )
}

predicate isReleaseOf(FunctionCall fc, Expr resourceExpr) {
  isReleaseName(fc.getTarget().getName()) and
  exists(Expr arg | arg = fc.getAnArgument() and sameStorage(resourceExpr, arg))
}

from
  AssignExpr acq, FunctionCall acqCall, Function f, ReturnStmt ret,
  FunctionCall releaseAfter, IfStmt errIf
where
  acq.getRValue() = acqCall and
  isAcquireName(acqCall.getTarget().getName()) and
  f = acq.getEnclosingFunction() and
  // pointer typed assignment
  acq.getLValue().getType().getUnspecifiedType() instanceof PointerType and
  // there is a release on the same storage somewhere in the function
  releaseAfter.getEnclosingFunction() = f and
  isReleaseOf(releaseAfter, acq.getLValue()) and
  // an error-conditional return between acquisition and release
  ret.getEnclosingFunction() = f and
  errIf.getEnclosingFunction() = f and
  ret.getParent*() = errIf.getThen() and
  // line ordering: acquire < if < release
  acq.getLocation().getStartLine() < errIf.getLocation().getStartLine() and
  errIf.getLocation().getStartLine() < releaseAfter.getLocation().getStartLine() and
  // no release-of-resource inside the then-branch of this if
  not exists(FunctionCall midRelease |
    midRelease.getEnclosingFunction() = f and
    isReleaseOf(midRelease, acq.getLValue()) and
    midRelease.getParent*() = errIf.getThen()
  ) and
  // no goto inside the then-branch either (i.e. truly a direct return)
  not exists(GotoStmt g | g.getParent*() = errIf.getThen()) and
  // exclude the null-check on the acquired pointer itself
  // (e.g. `if (!dwc->dwc3) return -ENOMEM;` after platform_device_alloc)
  not exists(Expr nullCheck |
    nullCheck = errIf.getCondition().getAChild*() and
    sameStorage(acq.getLValue(), nullCheck)
  )
select ret,
  "Possible resource leak: '" + acqCall.getTarget().getName() +
    "' at $@ is not released on this error-return path; release at $@ is skipped.",
  acq, "acquisition", releaseAfter, "release"
