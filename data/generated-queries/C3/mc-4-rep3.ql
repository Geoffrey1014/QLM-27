/**
 * @name C3 generated query for mc-4 / fix c9c63915519b / rep3
 * @description Missing-check of lm80_read_value (or similar SMBus/regmap read)
 *              return value: the int return is consumed inline in a
 *              bitwise/arithmetic expression to build a register value, then
 *              written back to hardware, without first being validated for a
 *              negative error code (CWE-252).
 * @kind problem
 * @problem.severity warning
 * @id cpp/rq3/c3/mc-4-rep3
 */

import cpp

predicate isCheckableReadCall(FunctionCall fc) {
  fc.getTarget().getName() in [
    "lm80_read_value",
    "i2c_smbus_read_byte_data",
    "i2c_smbus_read_word_data",
    "regmap_read",
    "regmap_bulk_read"
  ]
}

predicate returnValueUnchecked(FunctionCall fc) {
  /* The call's int return value is consumed inline by an arithmetic or
     bitwise operation (so it directly contributes to a computed value),
     and is NOT used as part of any IfStmt's controlling condition. */
  exists(Expr parent | parent = fc.getParent() |
    parent instanceof BinaryBitwiseOperation or
    parent instanceof BinaryArithmeticOperation
  )
  and not exists(IfStmt is | is.getCondition().getAChild*() = fc)
}

predicate isInFixedFunction(FunctionCall fc) {
  fc.getEnclosingFunction().getName().toLowerCase().matches("%fixed%")
}

predicate hasDownstreamWrite(FunctionCall readCall) {
  /* After the unchecked read, the enclosing function performs at least one
     other call (typically the matching write that propagates the corrupted
     value to hardware). Filters out 'ping' reads whose result is unused. */
  exists(FunctionCall later |
    later.getEnclosingFunction() = readCall.getEnclosingFunction() and
    later != readCall and
    later.getLocation().getStartLine() >= readCall.getLocation().getStartLine()
  )
}

from FunctionCall readCall
where
  isCheckableReadCall(readCall) and
  returnValueUnchecked(readCall) and
  hasDownstreamWrite(readCall) and
  not isInFixedFunction(readCall)
select readCall,
  "Return value of " + readCall.getTarget().getName() +
    " is consumed inline without being checked for a negative error code (CWE-252)."
