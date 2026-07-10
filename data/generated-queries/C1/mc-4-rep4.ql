/**
 * @name Missing check of error-returning call used directly in expression
 * @description A call to a function that returns a signed integer error
 *              code (e.g. an SMBus/I2C/regmap/bus read) is consumed
 *              directly inside an arithmetic / bitwise expression without
 *              first checking whether the return value indicates failure.
 *              Negative error codes will silently corrupt the surrounding
 *              computation.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-mc-4
 */

import cpp

/** Heuristic: a function whose name suggests it performs a fallible
 *  bus / hardware / register read or similar I/O that returns an int
 *  error code (negative on failure, value on success). */
bindingset[n]
predicate isErrorReturningName(string n) {
  n.matches("%_read%") or
  n.matches("%read_value%") or
  n.matches("%read_byte%") or
  n.matches("%read_word%") or
  n.matches("%read_block%") or
  n.matches("%smbus%") or
  n.matches("%i2c_%") or
  n.matches("%regmap%") or
  n.matches("%_recv%") or
  n.matches("%_get_%") or
  n.matches("%_xfer%") or
  n.matches("%_transfer%")
}

/** Holds if `e` is (or transitively contains) the call `fc` used as an
 *  operand of an arithmetic / bitwise / shift / comparison operation. */
predicate consumedInExpression(FunctionCall fc, Expr container) {
  (
    container instanceof BinaryArithmeticOperation or
    container instanceof BinaryBitwiseOperation or
    container instanceof ComparisonOperation or
    container instanceof UnaryBitwiseOperation
  ) and
  fc.getParent*() = container
}

from FunctionCall fc, Function callee, Expr container
where
  fc.getTarget() = callee and
  isErrorReturningName(callee.getName()) and
  // Returns a signed integer error-code style value.
  callee.getType().getUnspecifiedType() instanceof IntegralType and
  not callee.getType().getUnspecifiedType().(IntegralType).isUnsigned() and
  consumedInExpression(fc, container) and
  // Exclude the case where the call result is first compared against
  // an error sentinel (e.g. `if (foo() < 0)`), since that IS a check.
  not exists(ComparisonOperation cmp |
    fc.getParent*() = cmp and
    (
      cmp.getAnOperand().getValue().toInt() = 0 or
      cmp.getAnOperand() instanceof Literal
    )
  )
select fc,
  "Return value of '" + callee.getName() +
    "()' is used directly in an arithmetic/bitwise expression without " +
    "checking whether it indicates an error (negative return)."
