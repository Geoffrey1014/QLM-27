/**
 * @name Missing error check of SMBus/I2C read return value used in bit arithmetic
 * @description A function such as lm80_read_value() (and analogous i2c_smbus_read_*
 *              wrappers in hwmon drivers) returns a negative errno on failure or an
 *              unsigned data byte/word on success. Using its return value directly in
 *              arithmetic / bitwise expressions without first checking for a negative
 *              value lets the error code be silently masked into a register write,
 *              corrupting device state.
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
 * Heuristic: a function whose name suggests it reads a value from an SMBus / I2C /
 * device register and returns an int that may carry a negative errno on failure.
 * This covers the patched API (lm80_read_value) and its many siblings across
 * hwmon / i2c drivers (i2c_smbus_read_byte_data, i2c_smbus_read_word_data,
 * <drv>_read_value, <drv>_read_reg, regmap_read wrappers, etc.).
 */
predicate isSmbusReadLike(Function f) {
  f.getType().getUnspecifiedType() instanceof IntType and
  (
    f.getName().matches("%smbus_read%") or
    f.getName().matches("%i2c_read%") or
    f.getName().matches("%_read_value") or
    f.getName().matches("%_read_reg%") or
    f.getName().matches("%_read_byte%") or
    f.getName().matches("%_read_word%") or
    f.getName().matches("%_read_block%")
  ) and
  // Exclude trivially-typed accessors that obviously cannot fail negatively
  not f.getName().matches("%peek%")
}

/**
 * The call expression we care about: a direct call to one of the read-like
 * functions whose return type is a signed int (so a negative value is
 * representable and meaningful as an error).
 */
class SmbusReadCall extends FunctionCall {
  SmbusReadCall() {
    isSmbusReadLike(this.getTarget()) and
    this.getType().getUnspecifiedType() instanceof IntType
  }
}

/**
 * Holds if `e` is (or contains) the call `c` consumed by an arithmetic/bitwise
 * operation, an assignment, or a cast that loses the sign — i.e. the return value
 * is used without first being inspected for a negative error code.
 */
predicate usedInBitArith(SmbusReadCall c) {
  exists(Expr parent | parent = c.getParent() |
    parent instanceof BinaryBitwiseOperation or
    parent instanceof BinaryArithmeticOperation or
    parent instanceof UnaryBitwiseOperation or
    // Direct cast to an unsigned/narrow type that drops the sign bit, e.g.
    //   u8 reg = lm80_read_value(...);
    parent instanceof CStyleCast or
    parent instanceof Conversion
  )
  or
  // Stored into a variable whose declared type is unsigned/narrow.
  exists(Variable v |
    v.getInitializer().getExpr() = c or
    exists(AssignExpr a | a.getRValue() = c and a.getLValue() = v.getAnAccess())
  |
    v.getType().getUnspecifiedType().(IntegralType).isUnsigned() or
    v.getType().getSize() < any(IntType i).getSize()
  )
}

/**
 * Holds if there is a guard on the basic block of `c` (or a dominating block)
 * that tests the result of `c` (or a variable holding it) against < 0 / >= 0 /
 * IS_ERR-like predicate. We use a syntactic check on the enclosing function:
 * if the same call result (assigned to some variable) is compared to 0 with
 * a relational op anywhere on a path from the call to the offending use, treat
 * it as checked.
 */
predicate hasNegativeCheck(SmbusReadCall c) {
  // Case 1: the call sits inside the controlling expression of an `if` /
  // conditional that tests it against 0 directly:  if (foo(...) < 0) ...
  exists(IfStmt ifs, RelationalOperation rel |
    rel.getAChild*() = c and
    ifs.getCondition().getAChild*() = rel and
    rel.getAnOperand().getValue().toInt() = 0
  )
  or
  // Case 2: result stored in variable `v`, and `v` is subsequently compared
  // against 0 in the same function.
  exists(Variable v, RelationalOperation rel |
    (
      v.getInitializer().getExpr() = c or
      exists(AssignExpr a | a.getRValue() = c and a.getLValue() = v.getAnAccess())
    ) and
    rel.getAnOperand() = v.getAnAccess() and
    rel.getAnOperand().getValue().toInt() = 0 and
    rel.getEnclosingFunction() = c.getEnclosingFunction()
  )
  or
  // Case 3: IS_ERR / IS_ERR_OR_NULL-style macro/function on the value
  exists(FunctionCall fc |
    fc.getEnclosingFunction() = c.getEnclosingFunction() and
    fc.getTarget().getName().matches("IS_ERR%") and
    DataFlow::localExprFlow(c, fc.getAnArgument())
  )
}

from SmbusReadCall c
where
  usedInBitArith(c) and
  not hasNegativeCheck(c)
select c,
  "Return value of '" + c.getTarget().getName() +
    "' (which may be a negative errno) is used in arithmetic without a negative-value check."
