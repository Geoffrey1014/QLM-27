/**
 * @name Resource leak: allocated pointer dropped on early-exit error path without release
 * @description A local pointer variable is assigned the result of an
 *              allocation/acquire-style function call. On a later guarded
 *              error path inside the same function the variable goes out
 *              of scope via a return without any intervening release-style
 *              call on it. This matches the four-features memory-leak
 *              pattern (Lu).
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-lu-1
 */

import cpp

/** A "release-like" function call that takes v as an argument. */
predicate isReleaseCallOn(FunctionCall fc, Variable v) {
  fc.getAnArgument() = v.getAnAccess() and
  exists(string n | n = fc.getTarget().getName() |
    n.matches("%free%") or
    n.matches("kfree%") or
    n.matches("%_put") or
    n.matches("%_put_%") or
    n.matches("%_release%") or
    n.matches("%release_%") or
    n.matches("%_destroy") or
    n.matches("%_destroy_%") or
    n.matches("%_unref") or
    n.matches("%dealloc%")
  )
}

/** Heuristic: a function name that allocates / acquires a resource. */
bindingset[n]
predicate isAcquireName(string n) {
  n.matches("%alloc%") or
  n.matches("kmalloc%") or
  n.matches("kzalloc%") or
  n.matches("kcalloc%") or
  n.matches("%_create%") or
  n.matches("%_new") or
  n.matches("%_new_%") or
  n.matches("%_unpack%") or
  n.matches("%_get") or
  n.matches("%_get_%") or
  n.matches("%_acquire%") or
  n.matches("%_open") or
  n.matches("%_open_%") or
  n.matches("%_lookup") or
  n.matches("%_find_%") or
  n.matches("%_parse_phandle%")
}

from
  LocalVariable v, FunctionCall acq, ReturnStmt ret, Function f,
  IfStmt guard
where
  // v is a pointer
  v.getType().getUnspecifiedType() instanceof PointerType and
  // v is initialised or assigned from an acquire call
  (
    v.getInitializer().getExpr() = acq
    or
    exists(AssignExpr ae |
      ae.getLValue() = v.getAnAccess() and
      ae.getRValue() = acq
    )
  ) and
  isAcquireName(acq.getTarget().getName()) and
  f = acq.getEnclosingFunction() and
  ret.getEnclosingFunction() = f and
  // The return is the (or a) statement inside a guarding if's then-branch
  // i.e. an error-check style early exit, not the function's fallthrough.
  guard.getEnclosingFunction() = f and
  (
    ret = guard.getThen()
    or
    ret.getParent() = guard.getThen()
  ) and
  // Acquisition dominates the guard's condition (so v is in scope and live).
  acq.getASuccessor+() = guard.getCondition() and
  // The guarded condition is NOT a null-check on v itself
  // (those are normal "alloc failed -> return" paths, not leaks).
  not guard.getCondition().getAChild*() = v.getAnAccess() and
  // No release call on v occurs between acquisition and the return.
  not exists(FunctionCall rel |
    isReleaseCallOn(rel, v) and
    rel.getEnclosingFunction() = f and
    acq.getASuccessor+() = rel and
    rel.getASuccessor+() = ret
  ) and
  // The return is actually reachable from the acquisition.
  acq.getASuccessor+() = ret
select ret,
  "Potential resource leak: '" + v.getName() +
    "' acquired at $@ via '" + acq.getTarget().getName() +
    "' may be dropped on this early-return path without release.",
  acq, acq.getTarget().getName()
