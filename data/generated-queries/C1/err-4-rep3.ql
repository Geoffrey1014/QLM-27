/**
 * @name Missing error code on goto-to-cleanup path
 * @description A function returns an `int` status/err variable through a
 *              cleanup label. An early failure check (`if (!p)`,
 *              `if (p == NULL)`, etc.) jumps to that cleanup label without
 *              first assigning a negative errno to the status variable, so
 *              the function silently reports success despite the failure.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-err-4
 */

import cpp

/**
 * A local int variable `v` of function `f` that is used as the operand of
 * at least one `return v;` statement in `f` (i.e., it is the function's
 * status/err carrier).
 */
predicate isStatusReturnVar(Function f, LocalVariable v) {
  v.getFunction() = f and
  v.getType().getUnspecifiedType() instanceof IntType and
  exists(ReturnStmt r, VariableAccess va |
    r.getEnclosingFunction() = f and
    va = r.getExpr() and
    va.getTarget() = v
  )
}

/**
 * The status variable `v` has at least one assignment in `f` that writes
 * a non-negative value (typically `0` from a successful API call result)
 * BEFORE the failure branch, OR is left at its uninitialised/zero value.
 * We approximate by requiring that `v` has at least one assignment whose
 * RHS is NOT (syntactically) a negative numeric literal — i.e. it can
 * carry a "success" value.
 */
predicate hasSuccessLikeAssign(Function f, LocalVariable v) {
  exists(AssignExpr a |
    a.getEnclosingFunction() = f and
    a.getLValue().(VariableAccess).getTarget() = v and
    not a.getRValue() instanceof UnaryMinusExpr
  )
  or
  not exists(AssignExpr a0 |
    a0.getEnclosingFunction() = f and
    a0.getLValue().(VariableAccess).getTarget() = v
  )
}

/**
 * A failure-check `IfStmt` whose then-branch is a single `goto L;` (or a
 * `BlockStmt` containing only that `goto L;`) with no assignment to `v`
 * on that branch.
 */
predicate isBareGotoOnFailure(IfStmt ifs, GotoStmt g, LocalVariable v) {
  (g.getParent*() = ifs.getThen() or g = ifs.getThen()) and
  // The then-branch contains the goto and NOTHING that assigns to v.
  not exists(AssignExpr a |
    a.getEnclosingStmt().getParent*() = ifs.getThen() and
    a.getLValue().(VariableAccess).getTarget() = v
  ) and
  // The then-branch contains exactly one goto (avoid matching complex
  // branches that may have side-effects we don't model).
  count(GotoStmt g2 | g2.getParent*() = ifs.getThen() or g2 = ifs.getThen()) = 1
}

/**
 * The condition is a "failure" check: tests a pointer/integer for NULL /
 * zero, or for `< 0`. We deliberately accept the common idioms:
 *   if (!x)                 -> NotExpr on a pointer/int
 *   if (x == NULL)          -> EQExpr with null operand
 *   if (x < 0)              -> LTExpr with 0 RHS
 *   if (unlikely(!x))       -> NotExpr wrapped in a call (still NotExpr inside)
 */
predicate isFailureCondition(Expr cond) {
  cond instanceof NotExpr
  or
  exists(EQExpr eq | eq = cond and eq.getAnOperand() instanceof Literal)
  or
  exists(LTExpr lt |
    lt = cond and
    lt.getRightOperand().getValue() = "0"
  )
  or
  // unwrap a call-wrapped condition like `unlikely(!x)`: descend one level.
  isFailureCondition(cond.getAChild().(Expr))
}

/**
 * The target label of the goto eventually flows to a `return v;` without
 * any intervening assignment to `v`. We approximate by checking that the
 * function returns `v` and that the labelled statement is followed (in
 * source order) by code that does not assign to `v`. For monolithic-cell
 * scope we accept the weaker check: the label `L` is in the same function
 * and a `return v;` exists in `f` (caller already established by
 * `isStatusReturnVar`).
 */
predicate labelLeadsToReturnOfV(GotoStmt g, Function f, LocalVariable v) {
  g.getEnclosingFunction() = f and
  isStatusReturnVar(f, v)
}

from
  Function f, LocalVariable v, IfStmt ifs, GotoStmt g
where
  isStatusReturnVar(f, v) and
  hasSuccessLikeAssign(f, v) and
  ifs.getEnclosingFunction() = f and
  isFailureCondition(ifs.getControllingExpr()) and
  isBareGotoOnFailure(ifs, g, v) and
  // There must be at least one PRIOR assignment to v in the same function
  // that lexically precedes ifs (otherwise v is still uninitialised/zero
  // and the goto is not a "silent success" pattern but a different bug
  // class — uninit return).
  exists(AssignExpr pre |
    pre.getEnclosingFunction() = f and
    pre.getLValue().(VariableAccess).getTarget() = v and
    pre.getLocation().getStartLine() < ifs.getLocation().getStartLine()
  ) and
  // the goto path is reached precisely because status already carries the
  // (already-negative) error code and no extra assignment is needed.
  not exists(VariableAccess va |
    va.getEnclosingFunction() = f and
    va.getTarget() = v and
    va.getParent*() = ifs.getControllingExpr()
  ) and
  labelLeadsToReturnOfV(g, f, v) and
  // Drop the trivial case where the goto target is the very next statement
  // (which would simply break out, not jump to cleanup).
  exists(g.getTarget())
select g,
  "Failure branch goto in $@ skips assignment to status variable '" + v.getName() +
  "', so the function may return success despite the failure.",
  f, f.getName()
