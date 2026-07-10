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

/* A goto whose target dominates a return-of-err — approximates a
 * "common cleanup label" that joins multiple failure paths. */
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

/* Detect: an `if` whose condition is a failure-style test (a NULL/!E
 * check, or `E == 0`, or a bare variable test of a pointer-bearing
 * local) whose then-branch contains a `goto` to the cleanup label,
 * and along that branch no assignment to `err` occurs. */
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
  // No assignment to `err` between the `if` and its `goto`.
  not exists(Assignment a |
    a.getEnclosingFunction() = f and
    a.getLValue().(VariableAccess).getTarget() = err and
    a.getLocation().getStartLine() >= ifs.getLocation().getStartLine() and
    a.getLocation().getStartLine() <= g.getLocation().getStartLine()
  ) and
  // The goto target must be a shared cleanup epilogue: either reached
  // by another goto in the same function, OR followed by fall-through
  // to a later label that also runs cleanup (the cascading cleanup
  // pattern: `out_free_X:` ... `out_free_Y:` ...). We approximate the
  // cascading case by requiring that some *other* labeled statement
  // exists between the target label and the function-exit return — so
  // the target label is part of a multi-stage cleanup chain rather
  // than a standalone bail-out helper.
  exists(LabelStmt otherLab |
    otherLab.getEnclosingFunction() = f and
    otherLab != g.getTarget() and
    otherLab.getLocation().getStartLine() > g.getTarget().getLocation().getStartLine() and
    otherLab.getLocation().getStartLine() < ret.getLocation().getStartLine()
  )
select g,
  "Failure branch in '" + f.getName() +
  "' jumps to cleanup label '" + g.getName() +
  "' via `goto` without assigning an error code to return variable '" +
  err.getName() + "'; function will return 0 (success) on this failure path."
