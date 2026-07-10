/**
 * @name Missing error-code assignment before goto-to-return cleanup
 * @description A function returns an `int` error code that is initialized to 0
 *              (success). On an early-exit path the code performs `goto <out>`
 *              without first assigning a non-zero error code, yet the cleanup
 *              label ultimately executes `return err;`. The caller therefore
 *              sees success even though an error condition was detected.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-err-1
 */

import cpp

/**
 * Holds if `v` is the local variable that the enclosing function returns
 * at the cleanup label and that is initialized to a constant zero.
 */
predicate isErrSentinel(LocalVariable v, Function f) {
  v.getFunction() = f and
  v.getType().getUnspecifiedType() instanceof IntegralType and
  exists(Expr init | init = v.getInitializer().getExpr() |
    init.getValue().toInt() = 0
  ) and
  // The function returns this variable at some point.
  exists(ReturnStmt rs |
    rs.getEnclosingFunction() = f and
    rs.getExpr().(VariableAccess).getTarget() = v
  )
}

/**
 * Holds if `gs` is a goto statement guarded by a NULL-check on the result of
 * an acquire/lookup call, and no assignment to `v` precedes `gs` along the
 * guarded branch.
 */
predicate buggyGoto(GotoStmt gs, LocalVariable v, Function f) {
  gs.getEnclosingFunction() = f and
  isErrSentinel(v, f) and
  // The goto sits inside an `if` whose condition is a NULL-ish test.
  exists(IfStmt ifs, Expr cond | ifs.getThen().getAChild*() = gs or ifs.getThen() = gs |
    cond = ifs.getCondition() and
    (
      // !x  or  x == NULL  or  IS_ERR(x) style: the controlling expression
      // mentions a variable assigned from a call (acquire/lookup pattern).
      exists(LocalVariable lv, AssignExpr ae |
        ae.getLValue().(VariableAccess).getTarget() = lv and
        ae.getRValue() instanceof FunctionCall and
        cond.getAChild*().(VariableAccess).getTarget() = lv
      )
    )
  ) and
  // No assignment to `v` along the basic block(s) that reach `gs`
  // within the enclosing if-then.
  not exists(AssignExpr ae |
    ae.getLValue().(VariableAccess).getTarget() = v and
    ae.getEnclosingFunction() = f and
    ae.getLocation().getStartLine() < gs.getLocation().getStartLine() and
    // ensure the assignment is on the same guarded path: lies inside the
    // same `if`-then that contains the goto.
    exists(IfStmt ifs2, Stmt aeStmt |
      (ifs2.getThen().getAChild*() = gs or ifs2.getThen() = gs) and
      aeStmt = ae.getEnclosingStmt() and
      (ifs2.getThen().getAChild*() = aeStmt or ifs2.getThen() = aeStmt)
    )
  ) and
  // The goto target eventually leads to `return v;`.
  exists(ReturnStmt rs |
    rs.getEnclosingFunction() = f and
    rs.getExpr().(VariableAccess).getTarget() = v and
    rs.getLocation().getStartLine() >= gs.getTarget().getLocation().getStartLine()
  )
}

from GotoStmt gs, LocalVariable v, Function f
where buggyGoto(gs, v, f)
select gs,
  "Goto on early-exit path jumps to cleanup that returns '" + v.getName() +
    "' without assigning a non-zero error code; caller will see success."
