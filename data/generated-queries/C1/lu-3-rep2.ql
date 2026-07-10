/**
 * @name Runtime-PM / refcount get-sync without paired put on error path
 * @description A call to a runtime-PM (or similar refcount-style) get-sync
 *              function increments a reference counter even when it returns
 *              a negative error code. If the caller's failure branch simply
 *              returns / gotos without calling the matching release function
 *              on the same argument, the reference count is leaked.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-lu-3
 */

import cpp

/** A "get-sync"-style acquisition: the call increments a refcount whose
 *  release is required even when the call returns a negative error code. */
predicate isAcquireGetSync(FunctionCall fc) {
  exists(string n | n = fc.getTarget().getName() |
    n.matches("%get_sync%") or
    n.matches("pm_runtime_get%") or
    n.matches("%_resume_and_get") or
    n.matches("%runtime_resume_and_get")
  )
}

/** Heuristic matching of the release counterpart for a given acquisition. */
predicate isReleaseCounterpart(FunctionCall acq, FunctionCall rel) {
  rel.getEnclosingFunction() = acq.getEnclosingFunction() and
  rel.getArgument(0) = acq.getArgument(0).(VariableAccess).getTarget().getAnAccess() and
  exists(string n | n = rel.getTarget().getName() |
    n.matches("%_put%") or
    n.matches("%put_sync%") or
    n.matches("%put_noidle%") or
    n.matches("%put_autosuspend%")
  )
}

/** Does the statement `s` (transitively) contain a paired release call for `acq`? */
predicate containsRelease(Stmt s, FunctionCall acq) {
  exists(FunctionCall rel |
    isReleaseCounterpart(acq, rel) and
    rel.getEnclosingStmt().getParentStmt*() = s
  )
}

/** A return statement on the failure branch of an `if (ret < 0)` style
 *  check where `ret` is bound to the result of `acq`. */
predicate failureExitWithoutRelease(FunctionCall acq, Stmt exit) {
  exists(IfStmt iff, Variable retVar, Expr cond, Stmt thenBranch |
    // bind ret = acq()
    exists(Expr lhs |
      (
        exists(AssignExpr ae |
          ae.getRValue() = acq and
          ae.getLValue() = lhs
        )
        or
        exists(Initializer init |
          init.getExpr() = acq and
          init.getDeclaration() = retVar
        )
      ) and
      (lhs = retVar.getAnAccess() or retVar.getInitializer().getExpr() = acq)
    ) and
    iff.getEnclosingFunction() = acq.getEnclosingFunction() and
    cond = iff.getCondition() and
    // condition references retVar and looks like "< 0" / "!= 0" / "< something"
    cond.getAChild*() = retVar.getAnAccess() and
    (
      cond instanceof RelationalOperation
      or cond instanceof NEExpr
      or cond instanceof NotExpr
    ) and
    thenBranch = iff.getThen() and
    // an exit statement (return / goto) inside the then-branch
    (
      exit.(ReturnStmt).getEnclosingStmt().getParentStmt*() = thenBranch
      or exit.(GotoStmt).getEnclosingStmt().getParentStmt*() = thenBranch
      or exit = thenBranch.(ReturnStmt)
      or exit = thenBranch.(GotoStmt)
    ) and
    // the failure branch does NOT release
    not containsRelease(thenBranch, acq) and
    // and the acquisition lexically precedes the if
    acq.getLocation().getStartLine() < iff.getLocation().getStartLine() and
    acq.getEnclosingFunction() = exit.getEnclosingFunction()
  )
}

from FunctionCall acq, Stmt exit
where
  isAcquireGetSync(acq) and
  failureExitWithoutRelease(acq, exit)
select acq,
  "Runtime-PM/refcount acquisition '" + acq.getTarget().getName() +
  "' may leak: error-path exit at $@ returns without a matching release call.",
  exit, "exit"
