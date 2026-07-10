/**
 * @name Missing check of SMBus read return before use in bitmask expression
 * @description Detects calls to lm80_read_value / i2c_smbus_read_*_data whose
 *              return value (which may be a negative errno on I2C failure) is
 *              consumed directly inside a bitwise-AND expression without first
 *              being captured to a variable and checked for negativity.
 *              Pattern derived from upstream commit c9c63915519b
 *              ("hwmon: (lm80) fix a missing check of the status of SMBus read").
 * @kind problem
 * @problem.severity warning
 * @id qlm/l0-mc4-missing-check-smbus-read
 * @tags reliability
 *       missing-check
 */

import cpp

predicate isSmbusReadWrapper(FunctionCall fc) {
  fc.getTarget().getName() = "lm80_read_value" or
  fc.getTarget().getName() = "i2c_smbus_read_byte_data" or
  fc.getTarget().getName() = "i2c_smbus_read_word_data" or
  fc.getTarget().getName() = "i2c_smbus_read_block_data"
}

from FunctionCall fc, Function enclosing
where isSmbusReadWrapper(fc)
  and enclosing = fc.getEnclosingFunction()
  and exists(BitwiseAndExpr band | band.getAnOperand() = fc)
  and not exists(Variable v | v.getAnAssignedValue() = fc)
select fc,
  "Result of SMBus read " + fc.getTarget().getName() +
  " used directly in bitmask without prior negative-value check in " +
  enclosing.getName()
