/**
 * @name Missing check of SMBus/I2C read return value before arithmetic use
 * @description Detects calls to int-returning SMBus/I2C read helpers
 *              (`lm80_read_value`, `i2c_smbus_read_byte_data`, ...) whose
 *              result is fed directly into bitwise or arithmetic
 *              expressions (masking, OR, +, etc.) without first being
 *              tested for the negative error return.  Pattern derived
 *              from upstream commit c9c63915519b ("hwmon: (lm80) fix a
 *              missing check of the status of SMBus read").
 * @kind problem
 * @problem.severity warning
 * @id qlm/l0-mc4-missing-check-smbus-read
 * @tags reliability
 *       missing-check
 *       correctness
 */

import cpp

predicate isSmbusReadApi(FunctionCall fc) {
  fc.getTarget().getName() = "lm80_read_value" or
  fc.getTarget().getName() = "i2c_smbus_read_byte_data" or
  fc.getTarget().getName() = "i2c_smbus_read_word_data" or
  fc.getTarget().getName() = "i2c_smbus_read_block_data"
}

/** The call's return value flows directly into a bitwise / arithmetic
 *  expression (mask, OR, shift, arithmetic +) — the "used as data"
 *  shape from the buggy seed. */
predicate flowsIntoArithmetic(FunctionCall fc) {
  exists(BinaryOperation bo |
    bo.getAnOperand() = fc and
    (bo instanceof BitwiseAndExpr or
     bo instanceof BitwiseOrExpr  or
     bo instanceof BitwiseXorExpr or
     bo instanceof LShiftExpr     or
     bo instanceof RShiftExpr     or
     bo instanceof AddExpr        or
     bo instanceof SubExpr        or
     bo instanceof MulExpr)
  )
}

/** The call itself is the condition of an IfStmt / ConditionalExpr /
 *  logical operator — i.e. checked in place. */
predicate isCheckedInPlace(FunctionCall fc) {
  exists(IfStmt ifs | ifs.getCondition().getAChild*() = fc)
  or
  exists(ConditionalExpr c | c.getCondition().getAChild*() = fc)
  or
  exists(BinaryOperation bo |
    (bo instanceof ComparisonOperation or
     bo instanceof LogicalAndExpr or
     bo instanceof LogicalOrExpr)
    and bo.getAnOperand() = fc)
}

/** The call is assigned to a local variable, and that variable is
 *  compared / checked in an IfStmt or ConditionalExpr somewhere before
 *  the arithmetic use appears. Approximates "return value captured and
 *  then checked". */
predicate isCapturedAndChecked(FunctionCall fc) {
  exists(LocalVariable v, IfStmt ifs, VariableAccess va |
    v.getAnAssignedValue() = fc and
    ifs.getEnclosingFunction() = fc.getEnclosingFunction() and
    va.getTarget() = v and
    ifs.getCondition().getAChild*() = va
  )
  or
  exists(LocalVariable v, ConditionalExpr ce, VariableAccess va |
    v.getAnAssignedValue() = fc and
    ce.getEnclosingFunction() = fc.getEnclosingFunction() and
    va.getTarget() = v and
    ce.getCondition().getAChild*() = va
  )
  or
  exists(LocalVariable v, BinaryOperation bo, VariableAccess va |
    v.getAnAssignedValue() = fc and
    bo.getEnclosingFunction() = fc.getEnclosingFunction() and
    va.getTarget() = v and
    (bo instanceof ComparisonOperation or
     bo instanceof LogicalAndExpr or
     bo instanceof LogicalOrExpr) and
    bo.getAnOperand() = va
  )
}

from FunctionCall fc
where isSmbusReadApi(fc)
  and flowsIntoArithmetic(fc)
  and not isCheckedInPlace(fc)
  and not isCapturedAndChecked(fc)
select fc,
  "Missing check of SMBus/I2C read return value: '" +
  fc.getTarget().getName() +
  "()' flows into bitwise/arithmetic expression without prior negative-error check."
