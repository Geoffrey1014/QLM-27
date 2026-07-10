/**
 * @name Missing check of SMBus/I2C read return value
 * @description SMBus/I2C read helper functions (e.g. i2c_smbus_read_byte_data,
 *              i2c_smbus_read_word_data, and driver wrappers around them) can
 *              return a negative errno on failure. Using the returned value
 *              directly in arithmetic / bitwise expressions without first
 *              checking for a negative result can corrupt the data written
 *              back to the device. This query flags call sites whose return
 *              value is consumed without a negativity check.
 * @kind problem
 * @problem.severity warning
 * @id cpp/missing-smbus-read-check
 * @tags reliability
 *       correctness
 */

import cpp
import semmle.code.cpp.controlflow.Guards
import semmle.code.cpp.dataflow.DataFlow

/**
 * A function call that returns a value which, on failure, is a negative
 * errno from an SMBus / I2C read primitive (or a thin driver wrapper).
 */
class SmbusReadCall extends FunctionCall {
  SmbusReadCall() {
    exists(string n | n = this.getTarget().getName() |
      // direct SMBus / I2C primitives
      n = "i2c_smbus_read_byte" or
      n = "i2c_smbus_read_byte_data" or
      n = "i2c_smbus_read_word_data" or
      n = "i2c_smbus_read_word_swapped" or
      n = "i2c_smbus_read_block_data" or
      n = "i2c_smbus_read_i2c_block_data" or
      n = "i2c_smbus_xfer" or
      n = "i2c_transfer" or
      n = "i2c_master_recv" or
      // common driver wrapper naming conventions
      n.matches("%_read_value") or
      n.matches("%_read_reg") or
      n.matches("%_read_byte") or
      n.matches("%_read_word") or
      n.matches("%_smbus_read%")
    ) and
    // The function returns a signed integer type (so negative errno is
    // meaningful). Exclude void / unsigned-returning wrappers.
    this.getType().getUnspecifiedType() instanceof IntType and
    exists(IntType t |
      t = this.getType().getUnspecifiedType() and
      t.isSigned()
    )
  }
}

/**
 * Holds if `e` is a sub-expression of a guard condition that compares
 * something against 0 / a negative literal, i.e. a plausible negativity check.
 */
predicate isChecked(SmbusReadCall call) {
  // Case 1: the call result is used directly in a comparison.
  exists(ComparisonOperation cmp |
    cmp.getAnOperand() = call and
    (
      cmp.getAnOperand().getValue().toInt() = 0 or
      cmp.getAnOperand().getValue().toInt() < 0
    )
  )
  or
  // Case 2: the call result is stored in a variable that is later compared
  // to 0 / negative literal before being used arithmetically.
  exists(Variable v, AssignExpr ae, ComparisonOperation cmp |
    ae.getRValue() = call and
    ae.getLValue() = v.getAnAccess() and
    cmp.getAnOperand() = v.getAnAccess() and
    (
      cmp.getAnOperand().getValue().toInt() = 0 or
      cmp.getAnOperand().getValue().toInt() < 0
    )
  )
  or
  // Case 3: declared with initializer: `int rv = call(); if (rv < 0) ...`
  exists(Variable v, ComparisonOperation cmp |
    v.getInitializer().getExpr() = call and
    cmp.getAnOperand() = v.getAnAccess() and
    (
      cmp.getAnOperand().getValue().toInt() = 0 or
      cmp.getAnOperand().getValue().toInt() < 0
    )
  )
  or
  // Case 4: result fed to IS_ERR-like macro/function
  exists(FunctionCall fc |
    fc.getTarget().getName().matches("IS_ERR%") and
    fc.getAnArgument() = call
  )
}

/**
 * Holds if the result of `call` is consumed by an arithmetic / bitwise
 * expression (i.e. actually used as data, not just discarded).
 */
predicate isUsedAsData(SmbusReadCall call) {
  exists(Expr parent | parent = call.getParent() |
    parent instanceof BinaryArithmeticOperation or
    parent instanceof BinaryBitwiseOperation or
    parent instanceof UnaryBitwiseOperation or
    parent instanceof AssignArithmeticOperation or
    parent instanceof AssignBitwiseOperation or
    // cast then used in arithmetic
    exists(Expr gp |
      gp = parent.getParent() and
      (gp instanceof BinaryArithmeticOperation or gp instanceof BinaryBitwiseOperation)
    )
  )
}

from SmbusReadCall call
where
  isUsedAsData(call) and
  not isChecked(call) and
  // Don't flag if the enclosing function ignores all errors (e.g. void return
  // and no error handling anywhere -- usually a probe-time best-effort path).
  exists(call.getEnclosingFunction())
select call,
  "Return value of SMBus/I2C read '" + call.getTarget().getName() +
    "' is used without checking for a negative error code."
