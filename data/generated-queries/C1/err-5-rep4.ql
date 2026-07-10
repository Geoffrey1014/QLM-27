/**
 * @name Missing error code assignment before goto on allocation-failure branch
 * @description Detects a function-local `int` return variable that is
 *              initialised to zero and ultimately returned, where an
 *              `if (!ptr)` (or equivalent null/zero-check) guard on an
 *              error-handling branch performs a `goto` to a cleanup
 *              label without first assigning a non-zero (typically
 *              negative `-ENOMEM` / `-Exxx`) error value to that
 *              return variable. The function therefore reports success
 *              on a real failure path.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-err-5
 */

import cpp

/* A function-local variable initialised to 0 (or with no initialiser,
 * but later assigned 0) and ultimately returned via `return v;`. */
predicate isReturnedZeroInitLocal(Function f, LocalVariable v) {
  v.getFunction() = f and
  v.getType().getUnspecifiedType() instanceof IntegralType and
  exists(ReturnStmt rs |
    rs.getEnclosingFunction() = f and
    rs.getExpr().(VariableAccess).getTarget() = v
  ) and
  (
    not exists(v.getInitializer())
    or
    v.getInitializer().getExpr().getValue() = "0"
  )
}

/* Recursively: does statement `s` (or any of its descendants) contain
 * an assignment whose LHS is `v`? */
predicate containsAssignmentTo(Stmt s, LocalVariable v) {
  exists(Assignment a |
    a.getEnclosingStmt() = s and
    a.getLValue().(VariableAccess).getTarget() = v
  )
  or
  exists(Stmt child |
    child.getParentStmt() = s and
    containsAssignmentTo(child, v)
  )
}

/* True iff `cond` is a null / zero / not-test pattern typical of
 * error-handling guards on an allocator result. */
predicate isNullOrZeroTest(Expr cond) {
  cond instanceof NotExpr
  or
  exists(EQExpr e |
    e = cond and
    (
      e.getAnOperand().getValue() = "0"
      or
      e.getAnOperand() instanceof NullValue
    )
  )
  or
  exists(LEExpr le |
    le = cond and le.getRightOperand().getValue() = "0"
  )
  or
  exists(LTExpr lt |
    lt = cond and lt.getRightOperand().getValue() = "0"
  )
}

from Function f, LocalVariable ret, IfStmt guard, GotoStmt g
where
  /* `ret` is a zero-initialised int return variable of `f`. */
  isReturnedZeroInitLocal(f, ret) and
  /* `guard` is an error-handling if inside `f` whose condition is a
   * null / zero test (e.g. `!ptr`, `ptr == NULL`, `n < 0`). */
  guard.getEnclosingFunction() = f and
  isNullOrZeroTest(guard.getCondition()) and
  /* The guard's then-branch contains a `goto`. */
  g.getEnclosingFunction() = f and
  g.getParentStmt*() = guard.getThen() and
  /* The goto target sits inside the same function (a cleanup label). */
  g.getTarget().getEnclosingFunction() = f and
  /* No assignment to `ret` anywhere in the guard's then-branch
   * (so we transfer to cleanup carrying the stale 0). */
  not containsAssignmentTo(guard.getThen(), ret) and
  /* Heuristic narrowing: only flag when the cleanup path's terminal
   * statement is `return <ret>;` — i.e. the function really hands
   * the stale value back to its caller. (Always true by
   * isReturnedZeroInitLocal, kept here as documentation.) */
  exists(ReturnStmt rs |
    rs.getEnclosingFunction() = f and
    rs.getExpr().(VariableAccess).getTarget() = ret
  )
select g,
  "Error-handling 'goto' in function $@ transfers control to a cleanup label without assigning an error code to return variable '"
    + ret.getName() + "', so the function may return the success value 0 on a failure path.",
  f, f.getName()
