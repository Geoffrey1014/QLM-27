/**
 * @name Missing error-code assignment before goto-to-cleanup that returns the status variable
 * @description A function declares an `int` status variable initialized to 0
 *              (success).  Inside an `if` whose condition tests the result of
 *              a prior call (typical NULL/IS_ERR check on an acquire), the
 *              code performs `goto <label>` without first assigning a
 *              non-zero error code to that status variable.  The function
 *              ultimately executes `return <var>;`, so the caller observes
 *              success even though an error was detected on this path.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-err-5
 */

import cpp

/** A local int variable initialized to 0 that is returned by its function. */
predicate isStatusVar(LocalVariable v, Function f) {
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
 * The `if` statement `ifs` guards a control-flow path whose body is (or
 * contains) the goto `gs`, and the condition of `ifs` references a local
 * variable that was assigned from a function call earlier in the same
 * function — i.e. an acquire/lookup result is being checked.
 */
predicate guardedByAcquireCheck(IfStmt ifs, GotoStmt gs, Function f, LocalVariable status) {
  ifs.getEnclosingFunction() = f and
  (ifs.getThen() = gs or ifs.getThen().(Stmt).getAChild*() = gs) and
  // The status variable itself must NOT be tested in this condition —
  // we want to find checks of an acquire result, not error-propagation
  // checks like `if (ret < 0)`.
  not exists(VariableAccess va |
    va = ifs.getCondition().getAChild*() and va.getTarget() = status
  ) and
  // There exists a prior local that was assigned/initialized from a
  // FunctionCall and is referenced in the condition.
  exists(LocalVariable acq, VariableAccess condAcc |
    acq.getFunction() = f and
    acq != status and
    (
      // Initializer-as-assignment, e.g. `T *p = vzalloc(...);`
      acq.getInitializer().getExpr() instanceof FunctionCall
      or
      exists(AssignExpr ae |
        ae.getEnclosingFunction() = f and
        ae.getLValue().(VariableAccess).getTarget() = acq and
        ae.getRValue() instanceof FunctionCall and
        ae.getLocation().getStartLine() < gs.getLocation().getStartLine()
      )
    ) and
    condAcc = ifs.getCondition().getAChild*() and
    condAcc.getTarget() = acq
  )
}

/**
 * `gs` is preceded (statically) by no assignment to `v` inside the
 * enclosing then-branch of `ifs`.
 */
predicate noErrorAssignedOnPath(GotoStmt gs, IfStmt ifs, LocalVariable v) {
  not exists(AssignExpr ae |
    ae.getLValue().(VariableAccess).getTarget() = v and
    ae.getEnclosingFunction() = gs.getEnclosingFunction() and
    (ifs.getThen() = ae.getEnclosingStmt() or
     ifs.getThen().(Stmt).getAChild*() = ae.getEnclosingStmt()) and
    ae.getLocation().getStartLine() <= gs.getLocation().getStartLine()
  )
}

/** The goto target eventually leads to `return v;` in the same function. */
predicate gotoLeadsToReturnOfVar(GotoStmt gs, LocalVariable v) {
  exists(ReturnStmt rs |
    rs.getEnclosingFunction() = gs.getEnclosingFunction() and
    rs.getExpr().(VariableAccess).getTarget() = v and
    rs.getLocation().getStartLine() >= gs.getTarget().getLocation().getStartLine()
  )
}

from GotoStmt gs, LocalVariable v, Function f, IfStmt ifs
where
  f = gs.getEnclosingFunction() and
  isStatusVar(v, f) and
  guardedByAcquireCheck(ifs, gs, f, v) and
  noErrorAssignedOnPath(gs, ifs, v) and
  gotoLeadsToReturnOfVar(gs, v)
select gs,
  "Goto on guarded early-exit path jumps to cleanup that returns '" +
    v.getName() + "' without first assigning a non-zero error code; " +
    "caller will see success despite the failure."
