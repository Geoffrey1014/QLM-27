/**
 * @name Unchecked return value of error-returning device read used in expression
 * @description Detects calls to integer-returning device/SMBus read helpers
 *              whose return value (potentially a negative errno) is used
 *              directly inside an arithmetic/bitwise expression without being
 *              checked for an error condition. Such missing checks cause
 *              error codes to be silently incorporated into the computed
 *              value (e.g. masked into a register write payload).
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-mc-4
 */

import cpp

/**
 * Heuristic: integer-returning read helpers whose return value is an
 * error-or-data union (negative => errno, non-negative => data). These
 * are the APIs whose return value must be checked before use.
 */
predicate isErrorReturningReadApi(Function f) {
  f.getType().getUnspecifiedType() instanceof IntegralType and
  exists(string n | n = f.getName() |
    n.matches("%read_value%") or
    n.matches("%_read_byte%") or
    n.matches("%_read_word%") or
    n.matches("%_read_block%") or
    n.matches("smbus_read%") or
    n.matches("i2c_smbus_read%") or
    n.matches("regmap_read%") or
    n.matches("regmap_bulk_read%") or
    n.matches("regmap_raw_read%") or
    n.matches("%_read_reg%") or
    n.matches("read_reg%") or
    n.matches("%_reg_read%")
  )
}

/**
 * Holds if `fc` is a call whose return value is consumed inside a larger
 * arithmetic, bitwise, comparison-on-data, or assignment-to-data
 * expression — i.e. the value is being used as data rather than tested
 * as an error code.
 */
predicate returnUsedAsData(FunctionCall fc) {
  // Parent is a binary arithmetic / bitwise operation (mask, OR, shift, etc.)
  exists(BinaryOperation b |
    b.getAnOperand() = fc and
    (
      b instanceof BitwiseAndExpr or
      b instanceof BitwiseOrExpr or
      b instanceof BitwiseXorExpr or
      b instanceof AddExpr or
      b instanceof SubExpr or
      b instanceof MulExpr or
      b instanceof DivExpr or
      b instanceof LShiftExpr or
      b instanceof RShiftExpr
    )
  )
  or
  // Direct assignment of the raw call result to a data variable that is
  // then used without a < 0 / IS_ERR style check.
  exists(AssignExpr a | a.getRValue() = fc and
    not exists(IfStmt ig | ig.getEnclosingFunction() = fc.getEnclosingFunction() and
                           ig.getLocation().getStartLine() > fc.getLocation().getStartLine() and
                           ig.getLocation().getStartLine() < fc.getLocation().getStartLine() + 3))
}

/**
 * Holds if anywhere in `fc`'s enclosing function there is an explicit
 * error check on the return value (e.g. compared against 0 / < 0, or
 * passed to IS_ERR, or assigned to a variable subsequently compared).
 * If such a check exists, we consider the call already protected.
 */
predicate hasErrorCheckOnCall(FunctionCall fc) {
  // Call is the operand of a comparison expression directly.
  exists(ComparisonOperation cmp | cmp.getAnOperand() = fc)
  or
  // Call is the operand of a unary ! (used as boolean error check).
  exists(NotExpr n | n.getOperand() = fc)
  or
  // Call is wrapped in IS_ERR / IS_ERR_OR_NULL style macro/function call.
  exists(FunctionCall outer |
    outer.getAnArgument() = fc and
    outer.getTarget().getName().matches("IS_ERR%"))
}

from FunctionCall fc, Function callee
where
  callee = fc.getTarget() and
  isErrorReturningReadApi(callee) and
  returnUsedAsData(fc) and
  not hasErrorCheckOnCall(fc)
select fc,
  "Return value of '" + callee.getName() +
  "' may be a negative errno but is used directly in an expression without an error check."
