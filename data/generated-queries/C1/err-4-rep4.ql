/**
 * @name Missing error-code assignment before goto on NULL-result branch
 * @description A function holds an int "status" (or similar) variable that
 *              is initialized to 0 and is the value returned from a cleanup
 *              label. On a branch guarded by a NULL-check of an allocate /
 *              acquire call's result, control gotos the cleanup label
 *              without first assigning a non-zero error code to that
 *              variable, so the caller observes success even though
 *              allocation failed.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-err-4
 */

import cpp

/**
 * Holds if `v` is a local int variable in `f` that is initialized to a
 * constant zero and is the value of at least one ReturnStmt in `f` —
 * i.e. the "status / err" sentinel that the cleanup tail returns.
 */
predicate isErrSentinel(LocalVariable v, Function f) {
  v.getFunction() = f and
  v.getType().getUnspecifiedType() instanceof IntegralType and
  exists(Expr init | init = v.getInitializer().getExpr() |
    init.getValue().toInt() = 0
  ) and
  exists(ReturnStmt rs |
    rs.getEnclosingFunction() = f and
    rs.getExpr().(VariableAccess).getTarget() = v
  )
}

/**
 * Holds if `gs` is a goto inside an if-then whose condition is a NULL /
 * !-test of a local variable that was just assigned from a function call
 * (the acquire/alloc pattern), AND no assignment to the err sentinel `v`
 * appears anywhere in that same if-then branch before `gs`.
 */
predicate buggyGoto(GotoStmt gs, LocalVariable v, Function f) {
  gs.getEnclosingFunction() = f and
  isErrSentinel(v, f) and
  exists(IfStmt ifs, Expr cond |
    (ifs.getThen().getAChild*() = gs or ifs.getThen() = gs) and
    cond = ifs.getCondition() and
    // Controlling expression refers to a local variable that was
    // assigned from a function call (acquire/alloc semantics).
    exists(LocalVariable lv |
      cond.getAChild*().(VariableAccess).getTarget() = lv and
      (
        exists(AssignExpr ae |
          ae.getLValue().(VariableAccess).getTarget() = lv and
          ae.getRValue() instanceof FunctionCall and
          ae.getEnclosingFunction() = f
        )
        or
        // Initializer-form: T *x = call();
        exists(Expr ie |
          ie = lv.getInitializer().getExpr() and
          ie instanceof FunctionCall
        )
      )
    )
  ) and
  // No assignment to the err sentinel `v` sits on this guarded branch
  // before `gs` (in source order, within the same if-then subtree).
  not exists(AssignExpr ae, IfStmt ifs2, Stmt aeStmt |
    ae.getLValue().(VariableAccess).getTarget() = v and
    ae.getEnclosingFunction() = f and
    (ifs2.getThen().getAChild*() = gs or ifs2.getThen() = gs) and
    aeStmt = ae.getEnclosingStmt() and
    (ifs2.getThen().getAChild*() = aeStmt or ifs2.getThen() = aeStmt) and
    ae.getLocation().getStartLine() < gs.getLocation().getStartLine()
  ) and
  // The goto target ultimately reaches `return v;`.
  exists(ReturnStmt rs |
    rs.getEnclosingFunction() = f and
    rs.getExpr().(VariableAccess).getTarget() = v and
    rs.getLocation().getStartLine() >= gs.getTarget().getLocation().getStartLine()
  )
}

from GotoStmt gs, LocalVariable v, Function f
where buggyGoto(gs, v, f)
select gs,
  "Goto on NULL-result branch jumps to cleanup that returns '" + v.getName() +
    "' without first assigning a non-zero error code; caller will see success."
