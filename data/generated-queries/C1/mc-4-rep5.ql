/**
 * @name Missing check of SMBus/I2C read return value before bitwise use
 * @description A function returning a signed integer that may indicate an
 *              error via a negative return value is invoked, and its return
 *              value is consumed directly in an arithmetic or bitwise
 *              expression without being checked for a negative error.  If
 *              the call fails the negative errno will silently propagate
 *              into a register value or similar, corrupting subsequent
 *              hardware writes.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-mc-4
 * @tags correctness reliability
 */

import cpp

/**
 * A call whose target's name suggests an I/O / register / bus read that may
 * return a negative errno on failure.  We keep the name list deliberately
 * generic so the query will also flag analogous patterns outside the seed.
 */
predicate isErrorReturningReadCall(FunctionCall call) {
  exists(Function f | f = call.getTarget() |
    f.getType().getUnspecifiedType() instanceof IntType and
    (
      f.getName().toLowerCase().matches("%read_value%") or
      f.getName().toLowerCase().matches("%read_byte%") or
      f.getName().toLowerCase().matches("%read_word%") or
      f.getName().toLowerCase().matches("%read_reg%") or
      f.getName().toLowerCase().matches("%_read_block%") or
      f.getName().toLowerCase().matches("smbus_read%") or
      f.getName().toLowerCase().matches("i2c_smbus_read%")
    )
  )
}

/**
 * The call is used directly inside an arithmetic or bitwise expression
 * (i.e. the value flows into a computation without first being compared
 * against zero).  We detect this by walking up the AST parents and
 * looking for an arithmetic / bitwise binary operator that has the call
 * as an operand (possibly through implicit conversions).
 */
predicate usedInArithOrBitwise(FunctionCall call) {
  exists(Expr parent |
    parent = call.getParent+() and
    (
      parent instanceof BinaryBitwiseOperation or
      parent instanceof BinaryArithmeticOperation or
      parent instanceof UnaryBitwiseOperation
    ) and
    /* Confine to the nearest statement that contains the call so we don't
     * walk past a guard.  The expression's enclosing statement is the same
     * as the call's enclosing statement. */
    parent.getEnclosingStmt() = call.getEnclosingStmt()
  )
}

/**
 * The function enclosing the call performs no `< 0` check on the call's
 * return value (or on a temporary derived from it).  We approximate: there
 * exists no `RelationalOperation` in the same function whose left operand
 * is the call (or a variable assigned from the call) and whose right
 * operand is the literal 0.
 */
predicate hasNoNegativeCheck(FunctionCall call) {
  not exists(RelationalOperation rel |
    rel.getEnclosingFunction() = call.getEnclosingFunction() and
    rel.getRightOperand().getValue() = "0" and
    (
      rel.getLeftOperand() = call
      or
      exists(Variable v, AssignExpr ae |
        ae.getRValue() = call and
        ae.getLValue() = v.getAnAccess() and
        rel.getLeftOperand() = v.getAnAccess()
      )
      or
      /* Initializer-style: int rv = call; if (rv < 0) ... */
      exists(Variable v |
        v.getInitializer().getExpr() = call and
        rel.getLeftOperand() = v.getAnAccess()
      )
    )
  )
}

from FunctionCall call
where
  isErrorReturningReadCall(call) and
  usedInArithOrBitwise(call) and
  hasNoNegativeCheck(call)
select call,
  "Return value of '" + call.getTarget().getName() +
  "' is used in an arithmetic/bitwise expression without checking for a negative error code."
