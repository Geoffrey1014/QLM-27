/**
 * @name  rq3-c2-mc-4-rep4
 * @id    cpp/rq3/c2/mc-4-rep4
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects calls to failable SMBus/i2c read wrappers whose
 *              negative-error return value is consumed without a guarding
 *              "< 0" error check (missing-check pattern).
 */

import cpp
import semmle.code.cpp.controlflow.Guards

/**
 * A call to a function whose name matches a "failable read" pattern
 * (smbus/i2c/_read_value style helpers that return negative on error).
 */
predicate isFailableReadCall(FunctionCall fc) {
  exists(Function f | f = fc.getTarget() |
    (
      f.getName().matches("%read_value%") or
      f.getName().matches("%_read_byte%") or
      f.getName().matches("%_read_word%") or
      f.getName().matches("%_read_block%") or
      f.getName().matches("i2c_smbus_read%") or
      f.getName().matches("smbus_read%")
    ) and
    f.getType().getUnspecifiedType() instanceof IntType
  )
}

/**
 * The call's return value flows into an arithmetic / bitwise / assignment
 * expression where a negative error sentinel would corrupt the result.
 */
predicate returnValueUsedUnsafely(FunctionCall fc) {
  exists(Expr parent | parent = fc.getParent() |
    parent instanceof BinaryArithmeticOperation or
    parent instanceof BinaryBitwiseOperation or
    parent instanceof UnaryBitwiseOperation or
    parent instanceof AssignArithmeticOperation or
    parent instanceof AssignBitwiseOperation or
    (parent instanceof Assignment and
     not parent.(Assignment).getRValue() = fc.getParent().(ParenthesisExpr).getExpr())
  )
  or
  // Used as RHS of a plain assignment that then immediately feeds an arith/bitwise op
  exists(Assignment a, Variable v, Expr use |
    a.getRValue() = fc and
    a.getLValue() = v.getAnAccess() and
    use = v.getAnAccess() and
    use != a.getLValue() and
    (
      use.getParent() instanceof BinaryArithmeticOperation or
      use.getParent() instanceof BinaryBitwiseOperation
    )
  )
}

/**
 * There exists a guard in the same function that compares either the
 * call expression itself or any variable receiving the call to "< 0"
 * (i.e. an error check on the result).
 */
predicate hasErrorCheckGuard(FunctionCall fc) {
  exists(RelationalOperation cmp |
    cmp.getEnclosingFunction() = fc.getEnclosingFunction() and
    cmp.getRightOperand().getValue().toInt() = 0 and
    cmp.getOperator() = "<"
  |
    // direct check of the call's result
    cmp.getLeftOperand() = fc
    or
    // check of a variable that received the call's value
    exists(Variable v, Assignment a |
      a.getRValue() = fc and
      a.getLValue() = v.getAnAccess() and
      cmp.getLeftOperand() = v.getAnAccess()
    )
    or
    // check of an initialised variable
    exists(Variable v |
      v.getInitializer().getExpr() = fc and
      cmp.getLeftOperand() = v.getAnAccess()
    )
  )
}

/**
 * Main predicate: a failable read whose result is used unsafely with no
 * error-check guard anywhere in the enclosing function.
 */
predicate uncheckedFailableRead(FunctionCall fc) {
  isFailableReadCall(fc) and
  returnValueUsedUnsafely(fc) and
  not hasErrorCheckGuard(fc)
}

from FunctionCall fc
where uncheckedFailableRead(fc)
select fc,
  "Return value of failable read '" + fc.getTarget().getName() +
    "' is used without checking for a negative error code."
