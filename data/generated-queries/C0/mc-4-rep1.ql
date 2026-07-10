/**
 * @name Missing error check on SMBus/I2C read return value
 * @description The return value of an SMBus/I2C read helper (or analogous chip
 *              register read) can be negative on bus error. Using it directly
 *              in arithmetic/bitwise expressions without first testing for a
 *              negative result silently propagates the error code as data.
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
 * Functions whose return value encodes either a non-negative data byte/word read
 * from a hardware register, or a negative errno on failure. We match by name
 * suffix/prefix patterns common across the kernel I2C / SMBus / regmap APIs and
 * driver-local read wrappers built on top of them.
 */
predicate isHwReadFunction(Function f) {
  exists(string n | n = f.getName() |
    // i2c / smbus core
    n = "i2c_smbus_read_byte" or
    n = "i2c_smbus_read_byte_data" or
    n = "i2c_smbus_read_word_data" or
    n = "i2c_smbus_read_word_swapped" or
    n = "i2c_smbus_read_block_data" or
    n = "i2c_smbus_read_i2c_block_data" or
    n = "i2c_smbus_xfer" or
    // driver-local wrappers — the patched bug is in one of these
    n.matches("%_read_value") or
    n.matches("%_read_reg") or
    n.matches("%_reg_read") or
    n.matches("%_read_byte") or
    n.matches("%_read_word") or
    n.matches("%_read_block")
  ) and
  // must return a signed integer type that could legitimately be < 0
  f.getType().getUnspecifiedType() instanceof IntegralType and
  not f.getType().getUnspecifiedType().(IntegralType).isUnsigned()
}

/**
 * `e` is syntactically a guard that tests the sign / truthiness of `v`.
 */
predicate isNegativityCheck(Expr guard, Expr v) {
  exists(RelationalOperation rel | rel = guard |
    rel.getAnOperand() = v and
    rel.getAnOperand().getValue().toInt() <= 0
  )
  or
  exists(EqualityOperation eq | eq = guard |
    eq.getAnOperand() = v and
    eq.getAnOperand().getValue().toInt() < 0
  )
  or
  // `if (IS_ERR(...))` style or plain truthiness — be permissive on the
  // guard side so we minimise false positives.
  guard = v
}

/**
 * A direct use of a call result in an arithmetic / bitwise / index / assignment
 * context that would silently consume a negative errno as if it were data.
 */
predicate isDataUse(FunctionCall call, Expr use) {
  use = call and
  (
    exists(BinaryArithmeticOperation b | b.getAnOperand() = call) or
    exists(BinaryBitwiseOperation b | b.getAnOperand() = call) or
    exists(UnaryBitwiseOperation u | u.getOperand() = call) or
    exists(ArrayExpr a | a.getArrayOffset() = call) or
    // assignment to a narrower unsigned type loses the sign
    exists(AssignExpr a | a.getRValue() = call and
      a.getLValue().getType().getUnspecifiedType().(IntegralType).isUnsigned())
    or
    // initialiser of an unsigned variable
    exists(Variable v | v.getInitializer().getExpr() = call and
      v.getType().getUnspecifiedType().(IntegralType).isUnsigned())
  )
}

/**
 * Holds if there is some guard along a path that tests `call` for negativity
 * before `use`. We approximate by checking whether the enclosing function
 * contains *any* such guard syntactically referring back to the same call,
 * either directly or through an intermediate variable assignment.
 */
predicate hasNegativityGuardBefore(FunctionCall call, Expr use) {
  // direct: `if (call(...) < 0) ...` and the use is inside the then/else.
  exists(IfStmt ifs, Expr cond |
    cond = ifs.getCondition().getAChild*() and
    isNegativityCheck(cond, call)
  )
  or
  // via intermediate variable: `x = call(); if (x < 0) ...; ... use of x`
  exists(Variable v, Expr defE, IfStmt ifs, VariableAccess testVa |
    (
      v.getInitializer().getExpr() = call or
      exists(AssignExpr a | a.getLValue().(VariableAccess).getTarget() = v and a.getRValue() = call and defE = a)
    ) and
    testVa.getTarget() = v and
    isNegativityCheck(ifs.getCondition().getAChild*(), testVa)
  )
}

from FunctionCall call, Function callee, Expr use
where
  callee = call.getTarget() and
  isHwReadFunction(callee) and
  isDataUse(call, use) and
  not hasNegativityGuardBefore(call, use) and
  // exclude code inside ifdef'd-out branches and macro bodies we cannot
  // reason about cleanly
  exists(call.getFile().getRelativePath())
select call,
  "Return value of '" + callee.getName() +
  "' is used here in an arithmetic/bitwise context without a prior negative-error check; " +
  "if the read fails it returns a negative errno that will be silently consumed as data."
