/**
 * @name Allocated pointer leaked on early return from subsequent check
 * @description A pointer local variable is assigned from an allocation-style
 *              call; later, an `if (check(...)) return ...;` early-exit path
 *              returns without first releasing the pointer.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-lu-1
 */

import cpp

bindingset[n]
predicate isAllocLikeName(string n) {
  n.matches("%alloc%") or
  n.matches("%_create%") or
  n.matches("%_new%") or
  n.matches("make_%") or
  n.matches("%_make_%") or
  n.matches("%_open") or
  n.matches("%kzalloc%") or
  n.matches("%kmalloc%") or
  n.matches("%dup%") or
  n.matches("%unpack%") or
  n.matches("%_get") or
  n.matches("%_get_%") or
  n.matches("%_lookup") or
  n.matches("%_find_%") or
  n.matches("%parse_phandle%")
}

bindingset[n]
predicate isReleaseLikeName(string n) {
  n.matches("%_free%") or
  n.matches("free_%") or
  n.matches("kfree%") or
  n.matches("%_put") or
  n.matches("%_release%") or
  n.matches("%_destroy%") or
  n.matches("%_unref%") or
  n.matches("%_close") or
  n.matches("%_dispose%")
}

/* A release-like call whose argument expression syntactically references v. */
predicate releasesVar(FunctionCall rc, LocalVariable v) {
  isReleaseLikeName(rc.getTarget().getName()) and
  rc.getAnArgument().getAChild*() = v.getAnAccess()
}

from
  LocalVariable v, FunctionCall alloc, AssignExpr ae, IfStmt ifs, ReturnStmt ret,
  Function f
where
  // v is a pointer local assigned from an alloc-like call
  v.getType().getUnspecifiedType() instanceof PointerType and
  ae.getLValue() = v.getAnAccess() and
  ae.getRValue() = alloc and
  isAllocLikeName(alloc.getTarget().getName()) and
  f = ae.getEnclosingFunction() and
  // a later if-statement guards an early return
  ifs.getEnclosingFunction() = f and
  ae.getASuccessor+() = ifs and
  // the return is reached from inside the then-branch
  ret.getEnclosingFunction() = f and
  ret.getParent*() = ifs.getThen() and
  // the if-condition is NOT a (potentially negated) test of v itself
  not ifs.getCondition().getAChild*() = v.getAnAccess() and
  // no release of v on the path from alloc to the return
  not exists(FunctionCall rc |
    releasesVar(rc, v) and
    ae.getASuccessor+() = rc and
    rc.getASuccessor+() = ret
  ) and
  // exclude the case where the then-branch itself contains a release of v
  not exists(FunctionCall rc |
    releasesVar(rc, v) and
    rc.getEnclosingStmt().getParent*() = ifs.getThen()
  ) and
  // require some release of v elsewhere in the function (proves v must be released)
  exists(FunctionCall rc | releasesVar(rc, v) and rc.getEnclosingFunction() = f)
select ret,
  "Allocated pointer '" + v.getName() +
    "' may leak on this early return: assigned at $@ by call to '" +
    alloc.getTarget().getName() +
    "', no intervening release before return.",
  ae, "allocation"
