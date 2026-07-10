/**
 * @name Missing error code assignment on error goto path
 * @description Detects functions that branch to an error/cleanup label
 *              after a NULL-pointer check without assigning a negative
 *              error code to the return variable, causing the function
 *              to return 0 (success) despite an error condition.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-err-3
 */

import cpp

/**
 * Holds if `v` is a local variable used as the return value of `f`,
 * declared with `int` type and initialized to 0 (typical `int ret = 0`).
 */
predicate isErrRetVar(Function f, LocalVariable v) {
  v.getFunction() = f and
  v.getType().getUnspecifiedType() instanceof IntType and
  exists(Expr init | init = v.getInitializer().getExpr() |
    init.getValue().toInt() = 0
  ) and
  // v is returned from f
  exists(ReturnStmt rs | rs.getEnclosingFunction() = f |
    rs.getExpr().(VariableAccess).getTarget() = v
  )
}

/**
 * Holds if `assign` writes a negative integer value to `v` (i.e.
 * `v = -EXXX`).  We approximate "negative error code" by any unary
 * minus or constant whose evaluated value is negative.
 */
predicate assignsNegative(Assignment assign, LocalVariable v) {
  assign.getLValue().(VariableAccess).getTarget() = v and
  (
    assign.getRValue() instanceof UnaryMinusExpr
    or
    assign.getRValue().getValue().toInt() < 0
  )
}

/**
 * Holds if the body of `iff` (taken branch) contains a `goto`
 * (or `return` of `ret`) but does NOT assign a negative value to
 * `v` before that exit.
 */
predicate ifBodyMissesErrAssign(IfStmt iff, LocalVariable v, GotoStmt g) {
  g.getParentStmt*() = iff.getThen() and
  // No assignment of negative value to v anywhere in the then-branch
  not exists(Assignment a |
    a.getEnclosingStmt().getParentStmt*() = iff.getThen() and
    assignsNegative(a, v)
  )
}

/**
 * Holds if the condition of `iff` is a NULL-check of a pointer returned
 * by a lookup-like call (heuristic: condition is `!x` or `x == NULL`
 * where x is assigned by a function call returning a pointer).
 */
predicate isNullCheckOfLookup(IfStmt iff) {
  exists(VariableAccess va |
    (
      // `if (!x)`
      iff.getCondition().(NotExpr).getOperand() = va
      or
      // `if (x == NULL)` / `if (x == 0)`
      exists(EQExpr eq |
        eq = iff.getCondition() and
        eq.getAnOperand() = va and
        eq.getAnOperand().getValue().toInt() = 0
      )
    ) and
    va.getType().getUnspecifiedType() instanceof PointerType and
    // The variable was assigned from a function-call result (lookup)
    exists(Assignment a |
      a.getLValue().(VariableAccess).getTarget() = va.getTarget() and
      a.getRValue() instanceof FunctionCall
    )
  )
}

from Function f, LocalVariable ret, IfStmt iff, GotoStmt g
where
  isErrRetVar(f, ret) and
  iff.getEnclosingFunction() = f and
  g.getEnclosingFunction() = f and
  isNullCheckOfLookup(iff) and
  ifBodyMissesErrAssign(iff, ret, g) and
  // exclude trivially-empty if-bodies
  exists(Stmt s | s.getParentStmt*() = iff.getThen() and not s = iff.getThen())
select iff,
  "Error path branches to '" + g.getName() +
  "' without assigning a negative error code to return variable '" +
  ret.getName() + "' (in function $@).",
  f, f.getName()
