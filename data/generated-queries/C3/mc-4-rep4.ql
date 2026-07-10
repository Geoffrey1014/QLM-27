/**
 * @name Missing check of SMBus/regmap read-API return consumed inline as data
 * @description Detects calls to read-style register-access APIs whose int
 *              return value is consumed directly inside a bitwise or
 *              arithmetic expression (i.e. used as data) without ever being
 *              captured into a checkable int local. On hardware failure the
 *              API returns a negative error sentinel that gets silently
 *              folded into the computed value. Pattern derived from upstream
 *              commit c9c63915519b ("hwmon: (lm80) fix a missing check of
 *              the status of SMBus read").
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3/c3/missing-check-smbus-read-inline-use
 * @tags reliability
 *       missing-check
 */

import cpp

/* P1: read-style register-access APIs whose return signals success/failure. */
predicate isReadApi(FunctionCall fc) {
  fc.getTarget().getName() = "lm80_read_value" or
  fc.getTarget().getName() = "i2c_smbus_read_byte_data" or
  fc.getTarget().getName() = "i2c_smbus_read_word_data" or
  fc.getTarget().getName() = "regmap_read"
}

/* P2: the call's return is consumed *as data* — it is an operand of a
 *     bitwise or arithmetic BinaryOperation. Excludes comparison/relational
 *     parents (where the return is only used as a predicate). */
predicate consumedInlineAsData(FunctionCall fc) {
  exists(BinaryOperation bop |
    bop.getAnOperand() = fc and
    (bop instanceof BinaryBitwiseOperation or bop instanceof BinaryArithmeticOperation)
  )
}

/* P3: the call's return was captured into a local int variable (either via
 *     initialiser `int rv = call(...)` or assignment `rv = call(...)`).
 *     Used as a negative filter: if captured, the developer has the chance
 *     to check it elsewhere — we do not flag. */
predicate returnCapturedInIntLocal(FunctionCall fc) {
  exists(LocalVariable v |
    v.getInitializer().getExpr() = fc and
    v.getType().getUnspecifiedType() instanceof IntType
  )
  or
  exists(LocalVariable v, AssignExpr ae |
    ae.getRValue() = fc and
    ae.getLValue() = v.getAnAccess() and
    v.getType().getUnspecifiedType() instanceof IntType
  )
}

from FunctionCall fc
where isReadApi(fc) and
      consumedInlineAsData(fc) and
      not returnCapturedInIntLocal(fc)
select fc,
       "Unchecked SMBus/regmap read return consumed inline in a bitwise/"+
       "arithmetic expression (missing-check) in " +
       fc.getEnclosingFunction().getName()
