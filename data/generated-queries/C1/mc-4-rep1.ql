/**
 * @name Missing error check on integer-returning call used in arithmetic/bitwise expression
 * @description A function whose return type is a (signed) integer error code is
 *              invoked, and its return value is consumed directly by a
 *              bitwise / arithmetic operation without first being compared
 *              against zero or a negative value. Such call sites can silently
 *              mix error sentinels into computed data (e.g., a negative
 *              SMBus/regmap/i2c return value composed into a register value).
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-mc-4
 */

import cpp

/** Heuristic: callee name suggests a fallible read / xfer / probe / lookup
 *  / register-bank / hardware-status operation. */
bindingset[n]
predicate looksFallible(string n) {
  n.matches("%_read%") or
  n.matches("%_write%") or
  n.matches("%read_value%") or
  n.matches("%write_value%") or
  n.matches("%_xfer%") or
  n.matches("%_transfer%") or
  n.matches("%_bulk_%") or
  n.matches("%regmap%") or
  n.matches("%smbus%") or
  n.matches("%i2c_%") or
  n.matches("%_recv%") or
  n.matches("%_send%") or
  n.matches("%_get_%") or
  n.matches("%_set_%") or
  n.matches("%_probe%") or
  n.matches("%_request%") or
  n.matches("%_enable%") or
  n.matches("%_disable%")
}

/** A call to a function whose return type is a signed integer (typical
 *  kernel error-code convention: negative == error). */
predicate intReturningCall(FunctionCall fc) {
  exists(Function f |
    f = fc.getTarget() and
    looksFallible(f.getName()) and
    f.getType().getUnspecifiedType() instanceof IntegralType and
    not f.getType().getUnspecifiedType() instanceof BoolType and
    // Exclude pure void / pointer / floating returns by construction.
    f.getType().getSize() <= 8
  )
}

/** The call's value is consumed in a context that is *not* a check:
 *  bitwise / arithmetic operator, or initializer/assignment of a non-int
 *  destination (so an error sentinel would silently mix into computed data). */
predicate consumedUnchecked(FunctionCall fc) {
  exists(Expr parent | parent = fc.getParent() |
    // Arithmetic / bitwise operators
    parent instanceof BinaryArithmeticOperation or
    parent instanceof BinaryBitwiseOperation or
    parent instanceof UnaryBitwiseOperation or
    parent instanceof UnaryArithmeticOperation
  )
  and
  // Not directly inside a comparison-based check (callee result compared
  // to 0 or a negative literal).
  not exists(ComparisonOperation cmp |
    cmp.getAnOperand() = fc
  )
}

/** The enclosing function does not test the call's value before/after
 *  via an assignment-then-if pattern targeting the same expression. We
 *  approximate this by requiring there is no IfStmt in the same basic
 *  block whose condition references the call. */
predicate noNearbyCheck(FunctionCall fc) {
  not exists(IfStmt ifs |
    ifs.getEnclosingFunction() = fc.getEnclosingFunction() and
    ifs.getCondition().getAChild*() = fc
  )
}

from FunctionCall fc, Function callee
where
  callee = fc.getTarget() and
  intReturningCall(fc) and
  consumedUnchecked(fc) and
  noNearbyCheck(fc)
select fc,
  "Return value of '" + callee.getName() +
    "()' (int error code) is consumed by an arithmetic/bitwise expression " +
    "without being checked for failure first."
