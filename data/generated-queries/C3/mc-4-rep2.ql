/**
 * @name Missing check of lm80_read_value / SMBus read return value
 * @description Detects calls to read-style SMBus / lm80 helpers whose
 *              negative-on-error int return value is consumed *directly*
 *              as an operand of a bitwise or arithmetic operator at the
 *              call site (no intervening capture into a local variable
 *              that could be range-checked).  Pattern derived from
 *              upstream commit c9c63915519b ("hwmon: (lm80) fix a
 *              missing check of the status of SMBus read").
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3/c3/missing-check-lm80-read
 * @tags reliability
 *       missing-check
 */

import cpp

/* P1: target SMBus / lm80 read helpers whose int return encodes failure
 *     as a negative value. */
predicate isSmbusReadApi(FunctionCall fc) {
  fc.getTarget().getName() = "lm80_read_value" or
  fc.getTarget().getName() = "i2c_smbus_read_byte_data" or
  fc.getTarget().getName() = "i2c_smbus_read_word_data"
}

/* P2: the call expression itself is an operand of an arithmetic or
 *     bitwise binary operator — i.e. the int return is consumed in
 *     place, with no temporary that could be checked for `< 0`. */
predicate isUsedInArithExprUnchecked(FunctionCall fc) {
  exists(BinaryArithmeticOperation b | b.getAnOperand() = fc) or
  exists(BinaryBitwiseOperation b    | b.getAnOperand() = fc)
}

from FunctionCall fc
where isSmbusReadApi(fc) and
      isUsedInArithExprUnchecked(fc)
select fc,
       "Unchecked SMBus-read return value (" + fc.getTarget().getName() +
       ") used directly in arithmetic/bitwise expression in " +
       fc.getEnclosingFunction().getName() + " (missing-check)"
