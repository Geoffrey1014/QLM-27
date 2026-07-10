/**
 * @name Error-return missing on failure branch jumping to shared cleanup label
 * @description A function whose return value is an `int` local variable
 *   takes a `goto` to a shared cleanup epilogue on a detected failure
 *   branch (e.g. a NULL check on a freshly-allocated pointer) without
 *   assigning a non-zero error code to that variable. If the variable
 *   has not been set to an error value on that path, the function will
 *   return whatever it last held (often 0/success), masking the failure
 *   (CWE-394 / CWE-252 family).
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-err-4
 * @tags correctness reliability
 */

import cpp

/* An `int` local variable that the enclosing function returns by value
 * via a `return <var>;` statement at (one of) the function's exits. */
predicate isErrCodeVar(LocalVariable v, Function f) {
  v.getFunction() = f and
  v.getType().getUnspecifiedType() instanceof IntType and
  exists(ReturnStmt r |
    r.getEnclosingFunction() = f and
    r.getExpr().(VariableAccess).getTarget() = v
  )
}

/* A goto whose target label sits before a return-of-err in the same
 * function (textual approximation of "cleanup epilogue"). */
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

/* A failure-style if condition: `!E`, `E == 0`, or a bare variable
 * read used as a truthiness test. */
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
  // The if's then-body contains the goto (directly or through a block).
  g.getParentStmt*() = ifs.getThen() and
  isCleanupGoto(g, err) and
  ret.getEnclosingFunction() = f and
  ret.getExpr().(VariableAccess).getTarget() = err and
  // No assignment to `err` between the `if` and the `goto`.
  not exists(Assignment a |
    a.getEnclosingFunction() = f and
    a.getLValue().(VariableAccess).getTarget() = err and
    a.getLocation().getStartLine() >= ifs.getLocation().getStartLine() and
    a.getLocation().getStartLine() <= g.getLocation().getStartLine()
  ) and
  // Require that the target label is *shared* (reached by another goto).
  // This kills tiny helpers with a single bail-out.
  exists(GotoStmt other |
    other.getEnclosingFunction() = f and
    other != g and
    other.getTarget() = g.getTarget()
  )
select g,
  "Failure branch in '" + f.getName() +
  "' jumps to cleanup label '" + g.getName() +
  "' via `goto` without assigning an error code to return variable '" +
  err.getName() + "'; function may return stale/zero value on this failure path."
