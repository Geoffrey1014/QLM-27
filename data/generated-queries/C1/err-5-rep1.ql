/**
 * @name Error-return missing on failure branch jumping to common cleanup label
 * @description A function that returns an error code initializes its return
 *   variable to 0 (success), then on a detected failure branch (e.g. NULL
 *   check) jumps via `goto` to a common cleanup label without assigning a
 *   non-zero error code to the return variable. The function therefore
 *   returns success even though it failed (CWE-394 / CWE-252 family).
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-err-5
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

/* A goto whose target label sits before the final return of err in the
 * function (i.e. it is part of the cleanup epilogue). */
predicate isCleanupGoto(GotoStmt g, LocalVariable err) {
  exists(Function f, ReturnStmt r |
    g.getEnclosingFunction() = f and
    isErrCodeVar(err, f) and
    r.getEnclosingFunction() = f and
    r.getExpr().(VariableAccess).getTarget() = err and
    g.getTarget().getLocation().getStartLine() <
      r.getLocation().getStartLine() and
    g.getTarget().getEnclosingFunction() = f
  )
}

/* `if` whose condition is a failure-style test (a negation, an equality
 * against 0, or a bare local variable access used as a truthy guard). */
predicate failureCheck(IfStmt ifs) {
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
  g.getParentStmt*() = ifs.getThen() and
  isCleanupGoto(g, err) and
  ret.getEnclosingFunction() = f and
  ret.getExpr().(VariableAccess).getTarget() = err and
  // No assignment to `err` along the if-then branch up to the goto.
  not exists(Assignment a |
    a.getEnclosingFunction() = f and
    a.getLValue().(VariableAccess).getTarget() = err and
    a.getLocation().getStartLine() >= ifs.getLocation().getStartLine() and
    a.getLocation().getStartLine() <= g.getLocation().getStartLine()
  ) and
  // Require the cleanup label to be *shared* with at least one other goto:
  // kills tiny helpers that have exactly one bail-out.
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
