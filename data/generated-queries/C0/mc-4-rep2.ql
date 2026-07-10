/**
 * @name Missing error check of SMBus/I2C read return value
 * @description SMBus/I2C read helpers (e.g. lm80_read_value, i2c_smbus_read_byte_data,
 *              i2c_smbus_read_word_data, i2c_smbus_read_byte) return a negative errno on
 *              failure and otherwise the byte/word read. Using the returned value in an
 *              arithmetic or bitwise expression without checking for negative return causes
 *              the error code to be silently used as data, producing wrong register writes
 *              or corrupted sysfs output.
 * @kind problem
 * @problem.severity warning
 * @id cpp/missing-smbus-read-check
 * @tags reliability
 *       correctness
 */

import cpp
import semmle.code.cpp.controlflow.Guards
import semmle.code.cpp.controlflow.SSA

/**
 * SMBus/I2C-style read functions that return a negative errno on failure and the
 * data byte/word on success. Recognised by name pattern: either the kernel
 * `i2c_smbus_read_*` family, or a driver-local wrapper whose name ends in
 * `_read_value` / `_read_reg` / `_read_register` / `_read_byte` / `_read_word`.
 */
predicate isSmbusReadLike(Function f) {
  exists(string n | n = f.getName() |
    n = "i2c_smbus_read_byte" or
    n = "i2c_smbus_read_byte_data" or
    n = "i2c_smbus_read_word_data" or
    n = "i2c_smbus_read_word_swapped" or
    n = "i2c_smbus_read_block_data" or
    n = "i2c_smbus_read_i2c_block_data" or
    n.matches("%\\_read\\_value") or
    n.matches("%\\_read\\_reg") or
    n.matches("%\\_read\\_register") or
    n.matches("%\\_read\\_byte") or
    n.matches("%\\_read\\_word")
  ) and
  // Return type must be a signed integer so a negative errno is representable.
  f.getType().getUnspecifiedType() instanceof IntType and
  f.getType().getUnspecifiedType().(IntType).isSigned()
}

/** A call to an SMBus/I2C-style read function. */
class SmbusReadCall extends FunctionCall {
  SmbusReadCall() { isSmbusReadLike(this.getTarget()) }
}

/**
 * Holds if the value of `e` is guarded by a check that rejects negative values
 * (e.g. `if (e < 0) return e;`). Approximated by looking for any Guard
 * controlling `use` that mentions a comparison against zero of an expression
 * structurally equal to `e` or referring to the same SSA variable.
 */
predicate guardedAgainstNegative(Expr readExpr, Expr use) {
  exists(GuardCondition g, ComparisonOperation cmp |
    g = cmp and
    g.controls(use.getBasicBlock(), _) and
    (
      // direct check: readExpr < 0  /  readExpr >= 0
      cmp.getAnOperand().(Literal).getValue() = "0" and
      cmp.getAnOperand() != readExpr and
      // structurally references the same call result via a variable
      exists(SsaDefinition ssa, LocalScopeVariable v |
        ssa.getAUse(v) = cmp.getAnOperand().(VariableAccess) and
        ssa.getDefiningValue(v) = readExpr
      )
    )
  )
}

/**
 * Holds if `use` is an expression that consumes the value of the SMBus read
 * call `call` in a way that assumes success — i.e. arithmetic / bitwise use,
 * or assignment to a non-int destination (e.g. u8 register).
 */
predicate isDataConsumingUse(SmbusReadCall call, Expr use) {
  // direct use of the call result in bitwise / arithmetic context
  use = call and
  exists(Expr parent | parent = call.getParent() |
    parent instanceof BitwiseAndExpr or
    parent instanceof BitwiseOrExpr or
    parent instanceof BitwiseXorExpr or
    parent instanceof ComplementExpr or
    parent instanceof LShiftExpr or
    parent instanceof RShiftExpr or
    parent instanceof AddExpr or
    parent instanceof SubExpr or
    parent instanceof MulExpr or
    parent instanceof DivExpr or
    parent instanceof RemExpr or
    // assigned into a narrower (byte/word) destination
    exists(AssignExpr a | a = parent and
      a.getLValue().getType().getSize() < call.getType().getSize())
  )
}

from SmbusReadCall call, Expr use
where
  isDataConsumingUse(call, use) and
  not guardedAgainstNegative(call, use) and
  // Exclude calls whose result is captured into a variable that IS later
  // compared against 0 anywhere in the function — common idiom is to assign
  // then check; we keep only fully-inline unchecked uses.
  not exists(AssignExpr a, Variable v, ComparisonOperation cmp, Literal zero |
    a.getRValue() = call and
    a.getLValue() = v.getAnAccess() and
    cmp.getEnclosingFunction() = call.getEnclosingFunction() and
    cmp.getAnOperand() = v.getAnAccess() and
    zero = cmp.getAnOperand() and zero.getValue() = "0"
  )
select call,
  "Return value of SMBus/I2C read function '" + call.getTarget().getName() +
  "' is used without checking for a negative error code."
