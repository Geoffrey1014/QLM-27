/**
 * @name Missing error code on early-exit goto path
 * @description A function declares a local integer `err` initialized to 0,
 *              returns that variable at function exit, and contains a
 *              failure-check `if (!ptr) goto LABEL;` (or a similar negative
 *              check) which jumps to the return path without first assigning
 *              a non-zero error code to `err`. As a result the function
 *              silently returns success (0) on a real failure.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-err-1
 */

import cpp

/* The local integer variable that the function returns and that is
 * initialized to 0. */
predicate isZeroInitErrVar(LocalVariable v) {
  v.getType().getUnspecifiedType() instanceof IntegralType and
  exists(Expr init | init = v.getInitializer().getExpr() |
    init.getValue().toInt() = 0
  )
}

/* The function returns `v` (directly: `return v;`). */
predicate functionReturnsVar(Function f, LocalVariable v) {
  exists(ReturnStmt r, VariableAccess va |
    r.getEnclosingFunction() = f and
    va = r.getExpr() and
    va.getTarget() = v
  )
}

/* A `goto` statement that is "guarded" by a failure-style if-condition,
 * i.e. the goto is the (only) then-branch of an `if (!x)` / `if (x == 0)` /
 * `if (x == NULL)` style test on a freshly-assigned pointer or an
 * acquire-style call result. We approximate this as: `if (<cond>) goto L;`
 * where the condition is a NotExpr, an equality comparison against 0/NULL,
 * or a direct check whose operand has pointer type and was just assigned. */
predicate isFailureGuardedGoto(IfStmt ifs, GotoStmt gs) {
  (
    ifs.getThen() = gs
    or
    exists(BlockStmt b | ifs.getThen() = b and b.getStmt(0) = gs and b.getNumStmt() = 1)
  ) and
  (
    ifs.getCondition() instanceof NotExpr
    or
    exists(EQExpr eq | eq = ifs.getCondition() |
      eq.getAnOperand().getValue().toInt() = 0
    )
    or
    /* if (x == NULL) ... */
    exists(EqualityOperation eq | eq = ifs.getCondition() |
      eq.getAnOperand() instanceof NullValue
    )
    or
    /* if (IS_ERR(x)) goto out; */
    exists(FunctionCall fc | fc = ifs.getCondition() |
      fc.getTarget().getName().matches("%IS\\_ERR%") or
      fc.getTarget().getName().matches("IS_ERR%")
    )
  )
}

/* True if there is any assignment to `v` on a statement that appears
 * lexically inside `ifs` (i.e. on the failure path before the goto). */
predicate assignsErrInIf(IfStmt ifs, LocalVariable v) {
  exists(AssignExpr a, VariableAccess va |
    a.getEnclosingStmt().getParentStmt*() = ifs.getThen() and
    va = a.getLValue() and
    va.getTarget() = v
  )
}

from Function f, LocalVariable v, IfStmt ifs, GotoStmt gs
where
  isZeroInitErrVar(v) and
  v.getFunction() = f and
  functionReturnsVar(f, v) and
  gs.getEnclosingFunction() = f and
  isFailureGuardedGoto(ifs, gs) and
  ifs.getEnclosingFunction() = f and
  not assignsErrInIf(ifs, v) and
  /* Make sure the goto's target label is the same label whose body returns v
   * (avoids flagging mid-function gotos that jump to cleanup that assigns err
   * later). Approximation: any goto in f to a label that precedes the
   * function's return statement on v. */
  exists(LabelStmt lab, ReturnStmt r |
    gs.getTarget() = lab and
    r.getEnclosingFunction() = f and
    r.getExpr().(VariableAccess).getTarget() = v and
    lab.getLocation().getStartLine() <= r.getLocation().getStartLine()
  )
select gs,
  "Failure-guarded `goto` in function '" + f.getName() +
    "' jumps to the return path without assigning an error code to '" +
    v.getName() + "', so the function silently returns 0 on this failure path."
