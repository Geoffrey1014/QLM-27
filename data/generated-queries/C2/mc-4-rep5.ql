/**
 * @name  rq3-c2-mc-4-rep5
 * @id    cpp/rq3/c2/mc-4-rep5
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects calls to lm80_read_value (or similar may-fail int-returning
 *              SMBus read helpers) whose return value is used without first being
 *              checked for a negative error code.
 */

import cpp
import semmle.code.cpp.controlflow.Guards

/**
 * Holds if `f` is a may-fail accessor that returns a (possibly negative) error
 * code as a plain integer. We focus on the lm80 family but stay textual to
 * generalise across similar SMBus/I2C drivers.
 */
predicate isTargetReadApi(Function f) {
  f.getName() = "lm80_read_value"
}

/**
 * Holds if `fc` is a call to a target read API whose result enters the
 * surrounding expression directly (i.e. is not the call statement alone).
 */
predicate isTargetReadCall(FunctionCall fc) {
  isTargetReadApi(fc.getTarget()) and
  exists(Expr parent | parent = fc.getParent())
}

/**
 * Holds if `e` is a comparison of the form `x < 0`, `x <= -1`, `x < <const>` (const <= 0)
 * or the negation `x >= 0` that constitutes a check for a negative error code.
 */
predicate isNegativeErrorCheck(Expr e) {
  exists(RelationalOperation r | r = e |
    r.getLesserOperand().getValue().toInt() = 0
    or
    r.getGreaterOperand().getValue().toInt() = 0
    or
    r.getLesserOperand().getValue().toInt() < 0
    or
    r.getGreaterOperand().getValue().toInt() < 0
  )
}

/**
 * Holds if the value of call `fc` is guarded by a negative-error check before being used.
 * For C2 (no POC, AST-only) we approximate by: there exists a controlling guard expr
 * along the path from `fc` to its enclosing expression that calls isNegativeErrorCheck
 * on `fc` (or on a variable directly assigned from `fc`).
 */
predicate isGuardedByErrorCheck(FunctionCall fc) {
  exists(GuardCondition g, Expr checked |
    isNegativeErrorCheck(g) and
    (
      checked = fc
      or
      exists(Variable v |
        v.getAnAssignedValue() = fc and
        checked = v.getAnAccess()
      )
    ) and
    checked.getParent*() = g and
    g.controls(fc.getEnclosingStmt().getBasicBlock(), _)
  )
}

/**
 * The bug: a target read call whose value is consumed in an arithmetic/bit-mixing
 * expression without a preceding negative-error check.
 */
predicate isMissingCheckBug(FunctionCall fc) {
  isTargetReadCall(fc) and
  not isGuardedByErrorCheck(fc)
}

from FunctionCall fc
where isMissingCheckBug(fc)
select fc,
  "Return value of '" + fc.getTarget().getName() +
    "' is used without first being checked for a negative error code."
