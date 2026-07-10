/**
 * @name Error-return missing on failure branch jumping to common cleanup label
 * @description A function that returns an error code initializes its return
 *   variable to 0 (success), then on a detected failure branch (e.g. NULL
 *   check) jumps via `goto` to a common cleanup label without assigning a
 *   non-zero error code to the return variable. The function therefore
 *   returns success even though it failed (CWE-394 / CWE-252 family).
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-err-1
 * @tags correctness reliability
 */

import cpp

/* The return-code variable: a local int initialized to 0 and returned by
 * value at the end of the function. */
predicate isErrCodeVar(LocalVariable v, Function f) {
  v.getFunction() = f and
  v.getType().getUnspecifiedType() instanceof IntType and
  exists(Expr init | init = v.getInitializer().getExpr() |
    init.getValue().toInt() = 0
  ) and
  exists(ReturnStmt r | r.getEnclosingFunction() = f |
    r.getExpr().(VariableAccess).getTarget() = v
  )
}

/* A goto whose target's only statement is the return of the err var
 * (i.e. it is the common cleanup epilogue). */
predicate isCleanupGoto(GotoStmt g, LocalVariable err) {
  exists(Function f, ReturnStmt r |
    g.getEnclosingFunction() = f and
    isErrCodeVar(err, f) and
    r.getEnclosingFunction() = f and
    r.getExpr().(VariableAccess).getTarget() = err and
    // The goto target label is reached before the return; we approximate
    // "cleanup label" by requiring the labeled stmt to dominate that return
    // textually (label appears at a strictly earlier line and same function).
    g.getTarget().getLocation().getStartLine() <
      r.getLocation().getStartLine() and
    g.getTarget().getEnclosingFunction() = f
  )
}

/* Detect: an `if` whose condition is a failure-style test (a NULL check or
 * a negation of a call result) whose then-branch contains a `goto` to the
 * cleanup label, and along the branch no assignment to `err` occurs. */
predicate failureCheck(IfStmt ifs) {
  // condition is `!E` (NULL-style check) or `E == 0` or assignment then test.
  exists(Expr cond | cond = ifs.getCondition() |
    cond instanceof NotExpr
    or
    cond.(EQExpr).getAnOperand().getValue().toInt() = 0
    or
    cond.(VariableAccess).getTarget() instanceof LocalVariable
  )
}

from
  Function f, LocalVariable err, IfStmt ifs, GotoStmt g, ReturnStmt ret
where
  isErrCodeVar(err, f) and
  ifs.getEnclosingFunction() = f and
  failureCheck(ifs) and
  // The if's then-body (directly or via a single-stmt block) contains the goto.
  g.getParentStmt*() = ifs.getThen() and
  isCleanupGoto(g, err) and
  ret.getEnclosingFunction() = f and
  ret.getExpr().(VariableAccess).getTarget() = err and
  // No assignment to `err` along the path: between the start of the `if`'s
  // then-branch and the goto, there is no assignment whose lvalue is `err`.
  not exists(Assignment a |
    a.getEnclosingFunction() = f and
    a.getLValue().(VariableAccess).getTarget() = err and
    a.getLocation().getStartLine() >= ifs.getLocation().getStartLine() and
    a.getLocation().getStartLine() <= g.getLocation().getStartLine()
  ) and
  // err is initialized to 0 (already enforced by isErrCodeVar). Filter out
  // cases where the if-then assigns err to a non-zero literal — already
  // excluded by the "no assignment" clause.
  // Require that the goto target label is the same one used by other
  // (non-failure) gotos in the function — i.e. it is a *shared* cleanup,
  // not a one-off bail-out. This kills small helpers with a single goto.
  exists(GotoStmt other |
    other.getEnclosingFunction() = f and
    other != g and
    other.getTarget() = g.getTarget()
  )
select g,
  "Failure branch in '" + f.getName() +
  "' jumps to cleanup label '" + g.getName() +
  "' via `goto` without assigning an error code to return variable '" +
  err.getName() + "'; function will return 0 (success) on this failure path."
