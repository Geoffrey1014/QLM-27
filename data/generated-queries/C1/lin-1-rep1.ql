/**
 * @name Resource ref leak: acquired-in-loop pointer dropped without release on early-exit path
 * @description A pointer local variable assigned the result of an acquisition-style
 *              function call inside a loop body is dropped on some loop-body exit
 *              path (continue or break) without an intervening release call on that
 *              variable.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-lin-1
 */

import cpp

/** Heuristic: a "release-like" call taking variable v as an argument. */
predicate isReleaseCall(FunctionCall fc, Variable v) {
  fc.getAnArgument() = v.getAnAccess() and
  exists(string n | n = fc.getTarget().getName() |
    n.matches("%_put") or
    n.matches("%_free") or
    n.matches("free_%") or
    n.matches("kfree%") or
    n.matches("%release%") or
    n.matches("%_destroy") or
    n.matches("%_unref") or
    n.matches("%_unlock")
  )
}

/** Heuristic: an "acquire-like" function whose return value is a refcounted resource. */
bindingset[n]
predicate isAcquireFunctionName(string n) {
  n.matches("%_get") or
  n.matches("%_get_%") or
  n.matches("%_acquire") or
  n.matches("%parse_phandle%") or
  n.matches("%_lookup") or
  n.matches("%_find_%") or
  n.matches("%_open") or
  n.matches("%alloc%")
}

from AssignExpr ae, LocalVariable v, Loop loop, Stmt exit, FunctionCall acq
where
  ae.getLValue() = v.getAnAccess() and
  ae.getRValue() = acq and
  v.getType().getUnspecifiedType() instanceof PointerType and
  isAcquireFunctionName(acq.getTarget().getName()) and
  ae.getEnclosingFunction() = loop.getEnclosingFunction() and
  ae.getEnclosingStmt().getParentStmt+() = loop.getStmt() and
  (exit instanceof ContinueStmt or exit instanceof BreakStmt) and
  exit.getEnclosingFunction() = loop.getEnclosingFunction() and
  exit.getParentStmt+() = loop.getStmt() and
  // path from acquisition to exit
  ae.getASuccessor+() = exit and
  // no intervening release of v on any such path
  not exists(FunctionCall r |
    isReleaseCall(r, v) and
    ae.getASuccessor+() = r and
    r.getASuccessor+() = exit
  )
select exit,
  "Loop-acquired resource '" + v.getName() +
    "' may leak on this exit path: assigned at $@ by call to '" +
    acq.getTarget().getName() + "', with no intervening release.",
  ae, "acquisition"
