/**
 * @name C3 generated query for mc-4 / fix c9c63915519b / rep1
 * @description Missing-check of lm80_read_value (and related SMBus read APIs) return value used directly in an arithmetic/bitwise expression to compute a hardware register, without capturing into a variable and checking for a negative error code (CWE-252).
 * @kind problem
 * @problem.severity warning
 * @id cpp/rq3/c3/mc-4-rep1
 */

import cpp

predicate isCheckableReadCall(FunctionCall fc) {
  fc.getTarget().getName() in [
    "lm80_read_value",
    "lm75_read_value",
    "lm77_read_value",
    "lm78_read_value",
    "lm87_read_value",
    "lm90_read_value",
    "lm95234_read_value",
    "i2c_smbus_read_byte_data",
    "i2c_smbus_read_word_data"
  ]
}

predicate returnValueUsedInExpr(FunctionCall fc) {
  /* The call's int return value is consumed by a surrounding arithmetic or
     bitwise expression — i.e. the (possibly negative) result is folded into
     a value rather than being captured into a variable that could be
     subsequently checked. */
  exists(Expr parent | parent = fc.getParent() |
    parent instanceof BinaryArithmeticOperation or
    parent instanceof BinaryBitwiseOperation or
    parent instanceof UnaryBitwiseOperation
  )
}

predicate isInFixedFunction(FunctionCall fc) {
  fc.getEnclosingFunction().getName().toLowerCase().matches("%fixed%")
}

predicate notCapturedAndChecked(FunctionCall fc) {
  /* The call is not the RHS of a simple assignment / initialiser to a
     local variable. (If it were, that variable would typically be the
     subject of a subsequent error check, which is the fix pattern.) */
  not exists(AssignExpr ae | ae.getRValue() = fc) and
  not exists(Initializer init | init.getExpr() = fc)
}

from FunctionCall readCall
where
  isCheckableReadCall(readCall) and
  returnValueUsedInExpr(readCall) and
  notCapturedAndChecked(readCall) and
  not isInFixedFunction(readCall)
select readCall,
  "Return value of " + readCall.getTarget().getName() +
    " is used directly in an arithmetic/bitwise expression without being captured and checked for a negative error code (CWE-252)."
