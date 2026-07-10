/**
 * @name Missing error return code before goto to cleanup label
 * @description A function returns an `int` error code (via `return ret;`)
 *              but on at least one error path it does `goto cleanup;`
 *              inside an `if` body without first assigning a non-zero
 *              (typically negative errno) value to that return variable.
 *              The caller will see success even though the function
 *              detected an error condition.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-err-2
 */

import cpp

/**
 * The local int variable that the function returns directly via
 * `return v;`.  We use this as the "error code variable".
 */
predicate isReturnedIntVar(Function f, LocalVariable v) {
  v.getFunction() = f and
  v.getType().getUnspecifiedType() instanceof IntType and
  exists(ReturnStmt rs, VariableAccess va |
    rs.getEnclosingFunction() = f and
    rs.getExpr() = va and
    va.getTarget() = v
  )
}

/**
 * `v` is initialised to a compile-time-constant 0 at its declaration,
 * OR there is an explicit `v = 0` early-assignment somewhere in `f`.
 * Either way, in absence of a later assignment the value at any point
 * is 0 (= "no error").
 */
predicate retInitedZero(Function f, LocalVariable v) {
  isReturnedIntVar(f, v) and
  (
    v.getInitializer().getExpr().getValue().toInt() = 0
    or
    exists(AssignExpr ae |
      ae.getEnclosingFunction() = f and
      ae.getLValue().(VariableAccess).getTarget() = v and
      ae.getRValue().getValue().toInt() = 0
    )
  )
}

/**
 * A GotoStmt that is the (only) interesting body of an `if` (possibly
 * wrapped in a single-stmt block).  These are the "if (cond) goto X;"
 * error-handling sites of the four-features pattern.
 */
predicate ifGuardedGoto(IfStmt ifs, GotoStmt g) {
  g.getParent() = ifs.getThen()
  or
  exists(BlockStmt b |
    b = ifs.getThen() and
    b.getNumStmt() = 1 and
    b.getStmt(0) = g
  )
}

/**
 * The if-body that contains `g` writes to `v` (assignment).  If true,
 * the goto is NOT bug-shaped (programmer set the error code).
 */
predicate ifBodyAssignsVar(IfStmt ifs, LocalVariable v) {
  exists(AssignExpr ae |
    ae.getEnclosingStmt().getParentStmt*() = ifs.getThen() and
    ae.getLValue().(VariableAccess).getTarget() = v
  )
}

/**
 * The if-body that contains `g` exits the function via a `return`
 * with an explicit non-zero / negative value (e.g. `return -ENODEV;`).
 * Such an if-then is also NOT bug-shaped — it propagates an error.
 */
predicate ifBodyReturnsExplicit(IfStmt ifs) {
  exists(ReturnStmt rs |
    rs.getParentStmt*() = ifs.getThen() and
    exists(rs.getExpr())
  )
}

/**
 * The function uses `goto LABEL;` in several places as its cleanup
 * idiom — i.e. there is at least one OTHER goto to the same label
 * where the corresponding if-body DOES assign `v` to a negative-looking
 * value.  This is the JAWS "error-return-code" pattern signature:
 * sibling gotos prove the label is an error-cleanup label and `v`
 * is the carried error code.
 */
predicate hasErrorAssigningSiblingGoto(
  Function f, LocalVariable v, Stmt target
) {
  exists(GotoStmt sibling, IfStmt sibIf, AssignExpr ae |
    sibling.getEnclosingFunction() = f and
    sibling.getTarget() = target and
    ifGuardedGoto(sibIf, sibling) and
    ae.getEnclosingStmt().getParentStmt*() = sibIf.getThen() and
    ae.getLValue().(VariableAccess).getTarget() = v and
    (
      ae.getRValue() instanceof UnaryMinusExpr
      or
      ae.getRValue().getValue().toInt() < 0
    )
  )
}

from Function f, LocalVariable v, IfStmt ifs, GotoStmt g
where
  isReturnedIntVar(f, v) and
  retInitedZero(f, v) and
  g.getEnclosingFunction() = f and
  ifGuardedGoto(ifs, g) and
  // bug shape: this if-then neither assigns `v` nor returns with an
  // explicit value
  not ifBodyAssignsVar(ifs, v) and
  not ifBodyReturnsExplicit(ifs) and
  // proof the label IS an error-cleanup label (sibling goto sets `v`
  // to a negative value before jumping here)
  hasErrorAssigningSiblingGoto(f, v, g.getTarget())
select g,
  "Goto to cleanup label '" + g.getTarget().toString() +
    "' on error path inside function '" + f.getName() +
    "' does not assign an error code to return variable '" + v.getName() +
    "' first; caller will see success (= 0)."
