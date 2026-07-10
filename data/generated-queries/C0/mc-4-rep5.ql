/**
 * @name Missing error check on SMBus/i2c read return value
 * @description The result of an SMBus/i2c read helper (e.g. lm80_read_value,
 *              i2c_smbus_read_byte_data, i2c_smbus_read_word_data,
 *              i2c_smbus_read_word_swapped) may be a negative errno. Using the
 *              returned value without first checking for a negative result can
 *              corrupt subsequent register writes / mask computations and hide
 *              real I/O errors.
 * @kind problem
 * @problem.severity warning
 * @id cpp/missing-smbus-read-error-check
 * @tags reliability
 *       correctness
 */

import cpp
import semmle.code.cpp.controlflow.Guards
import semmle.code.cpp.dataflow.DataFlow

/**
 * A call whose return value can be a negative errno representing an I2C/SMBus
 * read failure. This covers the kernel's i2c_smbus_read_* helpers and any
 * driver-local wrapper whose name contains "read_value" / "read_reg" /
 * "smbus_read" and that returns a signed integer.
 */
class SmbusReadCall extends FunctionCall {
  SmbusReadCall() {
    exists(Function f | f = this.getTarget() |
      // canonical i2c_smbus_read_* helpers
      f.getName().matches("i2c_smbus_read_%")
      or
      // driver-local single-register read wrappers that return int / signed
      (
        (
          f.getName().matches("%_read_value") or
          f.getName().matches("%_read_reg%") or
          f.getName().matches("%smbus_read%")
        ) and
        f.getType().getUnderlyingType().(IntegralType).isSigned()
      )
    )
  }
}

/**
 * Holds if `e` is (transitively, through trivial conversions / parenthesised
 * expressions / simple assignments) checked against a negative value or
 * compared with `< 0` / `>= 0` / `IS_ERR` style guard in some condition that
 * dominates `use`.
 */
predicate isCheckedBefore(Expr defExpr, Expr use) {
  exists(GuardCondition g, Expr checked |
    g.controls(use.getBasicBlock(), _) and
    (
      // direct comparison: checked < 0  or  checked >= 0
      exists(RelationalOperation rel |
        rel = g or rel.getParent*() = g
      |
        rel.getAnOperand() = checked and
        rel.getAnOperand().getValue().toInt() = 0
      )
      or
      // equality with a negative literal:  checked == -EXXX
      exists(EqualityOperation eq |
        eq = g or eq.getParent*() = g
      |
        eq.getAnOperand() = checked
      )
    ) and
    (
      checked = defExpr
      or
      // checked is the same SSA-ish variable as defExpr's target
      exists(Variable v |
        v.getAnAccess() = checked and
        v.getAnAssignedValue() = defExpr
      )
    )
  )
}

/**
 * A use of the SMBus read result in an arithmetic / bitwise context (mask,
 * shift, OR, AND, write-back) — i.e. the value is being trusted as data, not
 * being inspected as an error code.
 */
predicate isDataUse(Expr use) {
  exists(BinaryBitwiseOperation b | b.getAnOperand() = use)
  or
  exists(AssignBitwiseOperation b | b.getAnOperand() = use)
  or
  exists(FunctionCall fc |
    fc.getAnArgument() = use and
    fc.getTarget().getName().matches("%_write%")
  )
}

from SmbusReadCall call, Expr use, Variable v
where
  // result of the call flows into a use
  (
    use = call // call result directly used (no temporary)
    or
    (
      v.getAnAssignedValue() = call and
      use = v.getAnAccess() and
      use.getEnclosingFunction() = call.getEnclosingFunction()
    )
  ) and
  isDataUse(use) and
  not isCheckedBefore(call, use) and
  // and there is no guard on `v` against negative anywhere before `use`
  not exists(GuardCondition g, RelationalOperation rel |
    g.controls(use.getBasicBlock(), _) and
    (rel = g or rel.getParent*() = g) and
    rel.getAnOperand() = v.getAnAccess() and
    rel.getAnOperand().getValue().toInt() = 0
  )
select call,
  "Return value of SMBus/i2c read '" + call.getTarget().getName() +
    "' is used at $@ without checking for a negative errno.", use, "this use"
