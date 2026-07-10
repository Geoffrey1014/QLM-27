/**
 * @name Missing check of SMBus/lm-family read return value used in bitwise expression
 * @description Detects calls to lm*_read_value / i2c_smbus_read_* whose int return
 *              value is consumed directly inside an arithmetic or bitwise expression
 *              without being captured into a variable that can then be checked for a
 *              negative error code (CWE-252).
 * @kind problem
 * @problem.severity warning
 * @id cpp/missing-check-smbus-read
 * @tags correctness
 *       security
 *       external/cwe/cwe-252
 */

import cpp

predicate isUncheckedReadValueUse(FunctionCall fc) {
  fc.getTarget().getName() in [
    "lm80_read_value",
    "lm75_read_value",
    "lm77_read_value",
    "lm78_read_value",
    "lm87_read_value",
    "lm90_read_value",
    "lm95234_read_value",
    "i2c_smbus_read_byte_data",
    "i2c_smbus_read_word_data"
  ] and
  exists(Expr parent | parent = fc.getParent() |
    parent instanceof BinaryArithmeticOperation or
    parent instanceof BinaryBitwiseOperation or
    parent instanceof UnaryBitwiseOperation
  ) and
  not exists(AssignExpr ae | ae.getRValue() = fc) and
  not exists(Initializer init | init.getExpr() = fc) and
  not fc.getEnclosingFunction().getName().toLowerCase().matches("%fixed%")
}

from FunctionCall readCall
where isUncheckedReadValueUse(readCall)
select readCall,
  "Return value of " + readCall.getTarget().getName() +
    " is used directly in an arithmetic/bitwise expression without being captured and checked for a negative error code (CWE-252)."
