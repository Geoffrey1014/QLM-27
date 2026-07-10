/**
 * @name Refcount leak: acquisition-style call whose error path returns without release
 * @description A call to an acquisition function (e.g., pm_runtime_get_sync,
 *              *_get_sync, *_get, *_acquire) that increments a reference even
 *              on failure is followed by a check on its return value, and on
 *              the failing branch the enclosing function returns without
 *              calling a corresponding release routine (e.g., *_put,
 *              *_release, *_unref).
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-lu-3
 */

import cpp

/** Heuristic: acquisition-style callee that increments a refcount even on error. */
bindingset[n]
predicate isAcquireName(string n) {
  n.matches("%_get_sync") or
  n.matches("%pm_runtime_get%") or
  n.matches("%_get") or
  n.matches("%_get_%") or
  n.matches("%_acquire")
}

/** Heuristic: matching release-style callee. */
bindingset[n]
predicate isReleaseName(string n) {
  n.matches("%_put") or
  n.matches("%_put_%") or
  n.matches("%_release") or
  n.matches("%_release_%") or
  n.matches("%_unref")
}

/** A call that "checks for failure" — the call's value flows into a comparison
 *  whose true-edge leads to an error return without release. We use a simple
 *  syntactic shape: the call result is assigned to a variable, the variable
 *  is compared with `< 0` / `!= 0`, and the true branch reaches a ReturnStmt
 *  without an intervening release call on the same argument. */
from
  FunctionCall acq, Variable ret, AssignExpr assign, IfStmt check,
  ReturnStmt errRet, Expr acqArg
where
  // acq is an acquisition-style call
  isAcquireName(acq.getTarget().getName()) and
  // its return value is assigned to a local variable
  assign.getRValue() = acq and
  assign.getLValue() = ret.getAnAccess() and
  // the argument used to acquire the resource (first arg, the device/handle)
  acqArg = acq.getArgument(0) and
  // an if-statement checks the returned variable for error
  exists(RelationalOperation cmp |
    check.getCondition().getAChild*() = cmp and
    cmp.getAnOperand() = ret.getAnAccess()
  ) and
  // the if's then-branch contains a return
  (errRet.getParentStmt*() = check.getThen() or errRet = check.getThen()) and
  // both belong to same function
  acq.getEnclosingFunction() = check.getEnclosingFunction() and
  acq.getEnclosingFunction() = errRet.getEnclosingFunction() and
  // assignment happens before the check (textually / control-flow)
  assign.getASuccessor+() = check and
  // no release call on the same acqArg between the check and the error return
  not exists(FunctionCall rel |
    isReleaseName(rel.getTarget().getName()) and
    rel.getEnclosingFunction() = acq.getEnclosingFunction() and
    rel.getASuccessor*() = errRet and
    check.getASuccessor*() = rel and
    // arguments structurally equal (same variable access or same expression text)
    (rel.getAnArgument().(VariableAccess).getTarget() =
       acqArg.(VariableAccess).getTarget()
     or
     rel.getAnArgument().toString() = acqArg.toString())
  ) and
  // and no release of the same acqArg anywhere earlier in the function on
  // this path (to avoid flagging cases where the release already happened)
  not exists(FunctionCall relEarly |
    isReleaseName(relEarly.getTarget().getName()) and
    relEarly.getEnclosingFunction() = acq.getEnclosingFunction() and
    relEarly.getASuccessor*() = errRet and
    relEarly.getASuccessor*() = check and
    (relEarly.getAnArgument().(VariableAccess).getTarget() =
       acqArg.(VariableAccess).getTarget()
     or
     relEarly.getAnArgument().toString() = acqArg.toString())
  )
select errRet,
  "Resource acquired by '" + acq.getTarget().getName() +
    "' at $@ may leak: error path returns without a matching release call.",
  acq, acq.getTarget().getName()
