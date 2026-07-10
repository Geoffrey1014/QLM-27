/**
 * @name Missing check of lm80_read_value / SMBus read return used inline in bitwise/arithmetic expression
 * @description Detects calls to read-style SMBus APIs (lm80_read_value,
 *              i2c_smbus_read_byte_data, smbus_read_byte) whose int
 *              return value is consumed directly in a bitwise or
 *              arithmetic expression without first being captured into
 *              a local variable and checked for a negative error
 *              sentinel. The masked-in negative value is then fed to a
 *              paired write-style API in the same function, corrupting
 *              hardware state on read failure. Pattern derived from
 *              upstream commit c9c63915519b ("hwmon: (lm80) fix a
 *              missing check of the status of SMBus read").
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3/c3/missing-check-lm80-smbus-read-inline
 * @tags reliability
 *       missing-check
 */

import cpp

/* P1: read-style APIs that return a negative int sentinel on error
 *     (and a small u8 register payload on success). */
predicate isReadApi(FunctionCall fc) {
  fc.getTarget().getName() = "lm80_read_value" or
  fc.getTarget().getName() = "smbus_read_byte" or
  fc.getTarget().getName() = "i2c_smbus_read_byte_data"
}

/* P2: paired write-style APIs that push a byte back to the hardware. */
predicate isWriteApi(FunctionCall fc) {
  fc.getTarget().getName() = "lm80_write_value" or
  fc.getTarget().getName() = "smbus_write_byte" or
  fc.getTarget().getName() = "i2c_smbus_write_byte_data"
}

/* P3: the call's return value flows directly into an arithmetic /
 *     bitwise binary expression — i.e. the caller never captured it
 *     into a local that could subsequently be tested for "< 0". A
 *     plain (void)-cast wrapper is treated the same way. */
predicate inlineUsedInArith(FunctionCall fc) {
  exists(BinaryArithmeticOperation b | b.getAnOperand() = fc) or
  exists(BinaryBitwiseOperation b   | b.getAnOperand() = fc) or
  exists(CStyleCast c | c.getExpr() = fc and
    (exists(BinaryArithmeticOperation b2 | b2.getAnOperand() = c) or
     exists(BinaryBitwiseOperation b2   | b2.getAnOperand() = c)))
}

/* P4: in the same function, a write-style API is called on a later
 *     line — i.e. whatever value we just inline-computed is about to
 *     be pushed back to hardware. */
predicate feedsWriteBack(FunctionCall fc) {
  exists(FunctionCall w, Function enclosing |
    enclosing = fc.getEnclosingFunction() and
    w.getEnclosingFunction() = enclosing and
    isWriteApi(w) and
    w.getLocation().getStartLine() > fc.getLocation().getStartLine())
}

from FunctionCall fc
where
  isReadApi(fc) and
  inlineUsedInArith(fc) and
  feedsWriteBack(fc)
select fc,
  "Unchecked SMBus-read return used inline in bitwise/arithmetic " +
  "expression and pushed back to hardware via " +
  "a paired write (missing-check) in " + fc.getEnclosingFunction().getName()
