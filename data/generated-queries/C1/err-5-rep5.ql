/**
 * @name Missing error return code before goto on error branch
 * @description Detects functions returning an int status variable
 *              where, on an error-handling branch guarded by a NULL
 *              / zero check, control transfers via `goto` to a
 *              cleanup label without first assigning a (negative)
 *              error code to the return variable, so the function
 *              returns a stale value (often 0 / success) on an error
 *              path.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-err-5
 */

import cpp

/* A local variable that the enclosing function ultimately returns
 * (the "status / return code" variable). */
predicate isReturnedLocal(Function f, LocalVariable v) {
  v.getFunction() = f and
  exists(ReturnStmt rs, VariableAccess va |
    rs.getEnclosingFunction() = f and
    va = rs.getExpr() and
    va.getTarget() = v
  )
}

/* True if `s` (or any statement nested inside it) assigns to `v`. */
predicate stmtAssigns(Stmt s, LocalVariable v) {
  exists(Assignment a |
    a.getEnclosingStmt() = s and
    a.getLValue().(VariableAccess).getTarget() = v
  )
  or
  exists(Stmt child |
    child.getParentStmt() = s and stmtAssigns(child, v)
  )
}

/* The IfStmt is an error-handling guard: condition is a NULL / zero
 * test on some value (NotExpr, EQExpr to 0/NULL, or `<= 0`). */
predicate isErrorGuard(IfStmt is) {
  is.getCondition() instanceof NotExpr
  or
  exists(EQExpr e | e = is.getCondition() and
    (e.getAnOperand().getValue() = "0" or e.getAnOperand() instanceof NullValue))
  or
  exists(LEExpr le | le = is.getCondition() and
    le.getRightOperand().getValue() = "0")
  or
  exists(LTExpr lt | lt = is.getCondition() and
    lt.getRightOperand().getValue() = "0")
}

from Function f, LocalVariable ret, IfStmt guard, GotoStmt g
where
  /* f returns an int status variable */
  isReturnedLocal(f, ret) and
  ret.getType().getUnspecifiedType() instanceof IntegralType and

  /* `guard` is an error-handling if inside f */
  guard.getEnclosingFunction() = f and
  isErrorGuard(guard) and

  /* The then-branch of `guard` contains a goto */
  g.getEnclosingFunction() = f and
  (g.getParentStmt*() = guard.getThen()) and

  /* The goto target eventually executes `return <ret>` without an
   * intervening assignment of `ret` between the label and the
   * return.  Approximation: the label's enclosing function has a
   * ReturnStmt of `ret`, and the goto target label sits on the
   * cleanup path that reaches that ReturnStmt. */
  exists(Stmt labelTarget |
    labelTarget = g.getTarget() and
    labelTarget.getEnclosingFunction() = f
  ) and

  /* The body of the guard does NOT assign `ret` before the goto. */
  not stmtAssigns(guard.getThen(), ret) and

  /* Exclude the case where `ret` is assigned a non-zero literal at
   * its declarator initialiser (so the stale value would be a real
   * error code). Conservative: only flag when initialiser is 0 or
   * absent. */
  (
    not exists(ret.getInitializer())
    or
    ret.getInitializer().getExpr().getValue() = "0"
  )

select g,
  "Goto in error branch of function $@ transfers control to cleanup without assigning error code to return variable '"
    + ret.getName() + "'.",
  f, f.getName()
