/**
 * @name Refcount leak: acquire-style call's error path returns without releasing
 * @description An acquire-style API (e.g., a *_get_sync / *_get function that
 *              bumps a refcount or PM-runtime counter even on failure) is
 *              checked for `< 0` and the error path returns immediately
 *              without calling the matching release routine on the same
 *              device/object, leaking the counter.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-lu-3
 */

import cpp
import semmle.code.cpp.valuenumbering.GlobalValueNumbering

/** Heuristic: acquire-style function that returns int and whose name
 *  suggests it increments a counter (e.g., pm_runtime_get_sync, *_get_sync,
 *  *_get, *_resume_and_get). */
bindingset[n]
predicate isAcquireName(string n) {
  n.matches("%_get_sync") or
  n.matches("%_get") or
  n.matches("%_resume_and_get") or
  n.matches("%pm_runtime_get%") or
  n.matches("%_acquire")
}

/** Heuristic: release routine corresponding to an acquire. */
bindingset[a, r]
predicate isMatchingReleaseName(string a, string r) {
  // pm_runtime_get* -> pm_runtime_put*
  (a.matches("%pm_runtime_get%") and r.matches("%pm_runtime_put%"))
  or
  // generic *_get -> *_put / *_unref / *_release
  (a.matches("%_get_sync") and (r.matches("%_put%") or r.matches("%_put_sync%")))
  or
  (a.matches("%_get") and (r.matches("%_put%") or r.matches("%_unref%") or r.matches("%_release%")))
  or
  (a.matches("%_acquire") and r.matches("%_release%"))
  or
  (a.matches("%_resume_and_get") and r.matches("%_put%"))
}

/** A FunctionCall whose return value is assigned to a local variable,
 *  then compared `< 0` (or `< constant 0`) inside an IfStmt whose then-
 *  branch is/contains a ReturnStmt that does NOT call any release. */
from
  FunctionCall acq, Function enc, LocalVariable ret, AssignExpr assign,
  IfStmt ifst, RelationalOperation cmp, ReturnStmt rs, Expr devArg
where
  enc = acq.getEnclosingFunction() and
  isAcquireName(acq.getTarget().getName()) and
  acq.getTarget().getType().getUnderlyingType() instanceof IntegralType and
  acq.getNumberOfArguments() >= 1 and
  devArg = acq.getArgument(0) and
  // assign: ret = acq(...)
  assign.getRValue() = acq and
  assign.getLValue() = ret.getAnAccess() and
  // if (ret < 0) ...
  ifst.getEnclosingFunction() = enc and
  cmp = ifst.getCondition() and
  cmp.getOperator() = "<" and
  cmp.getLeftOperand() = ret.getAnAccess() and
  cmp.getRightOperand().getValue().toInt() = 0 and
  // return inside then-branch
  rs.getEnclosingStmt().getParentStmt*() = ifst.getThen() and
  // and that then-branch contains NO call to a matching release on the
  // same first-argument
  not exists(FunctionCall rel |
    rel.getEnclosingFunction() = enc and
    rel.getEnclosingStmt().getParentStmt*() = ifst.getThen() and
    isMatchingReleaseName(acq.getTarget().getName(), rel.getTarget().getName()) and
    // best-effort: same first argument syntactically
    rel.getNumberOfArguments() >= 1 and
    globalValueNumber(rel.getArgument(0)) = globalValueNumber(devArg)
  ) and
  // sanity: the assignment dominates the if
  assign.getASuccessor+() = ifst
select rs,
  "Error path of acquire-style call '" + acq.getTarget().getName() +
    "' returns without calling matching release on its first argument; " +
    "potential refcount leak.",
  acq, "acquired here"
