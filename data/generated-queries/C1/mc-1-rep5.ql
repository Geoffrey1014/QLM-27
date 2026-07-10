/**
 * @name Missing return-value check after regmap bulk/read accessor
 * @description regmap_*_read and similar accessors return a negative
 *              errno on failure and populate an output buffer only on
 *              success. Discarding the return value and using the
 *              output buffer regardless leads to acting on uninitialised
 *              or stale data when the underlying bus transaction fails.
 *              (CWE-252.)
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-mc-1
 */

import cpp

/**
 * APIs that return an int errno where 0 == success and a non-zero
 * value means the output argument(s) were NOT populated. Their return
 * value MUST be checked before the output arg is consumed.
 */
predicate isErrnoReadAccessor(string name) {
  name = "regmap_bulk_read" or
  name = "regmap_read" or
  name = "regmap_raw_read" or
  name = "regmap_noinc_read" or
  name = "regmap_fields_read" or
  name = "regmap_multi_reg_read" or
  name = "i2c_smbus_read_byte_data" or
  name = "i2c_smbus_read_word_data" or
  name = "i2c_smbus_read_block_data"
}

/**
 * Holds if `c` appears as an `ExprStmt` — i.e. its return value is
 * syntactically discarded (not assigned, not used in a condition, not
 * passed to another call, etc.).
 */
predicate returnValueDiscarded(FunctionCall c) {
  exists(ExprStmt s | s.getExpr() = c)
}

/**
 * The output buffer argument: for the supported APIs above the buffer
 * argument is at index 2 (regmap_bulk_read / regmap_raw_read /
 * regmap_noinc_read / regmap_multi_reg_read), index 1 (regmap_read,
 * regmap_fields_read), or index 1 (i2c_smbus_read_*_data). We
 * conservatively pick any pointer-typed argument whose pointee is then
 * accessed after the call in the same function — that is the data we
 * are accusing the caller of trusting blindly.
 */
predicate isPointerArg(FunctionCall c, Expr arg) {
  exists(int i, Type t |
    arg = c.getArgument(i) and
    t = arg.getType().getUnspecifiedType() and
    (t instanceof PointerType or t instanceof ArrayType)
  )
}

/**
 * Holds if `c` passes a pointer to some named storage (either a local
 * variable or a struct field) and that same named storage is read
 * later in the same function. This models "the caller goes on to use
 * the buffer the failed accessor was supposed to fill".
 *
 * We collapse both VariableAccess (local) and FieldAccess (struct
 * field) into a single Declaration so the predicate works whether the
 * buffer lives on the stack or inside a context struct.
 */
predicate outBufferLaterUsed(FunctionCall c, Declaration d) {
  exists(Expr outArg, Expr inner |
    isPointerArg(c, outArg) and
    // Peel off optional address-of.
    (
      inner = outArg.(AddressOfExpr).getOperand() or
      inner = outArg
    ) and
    (
      d = inner.(VariableAccess).getTarget() or
      d = inner.(FieldAccess).getTarget()
    )
  ) and
  exists(Expr later |
    later.getEnclosingFunction() = c.getEnclosingFunction() and
    later.getLocation().getStartLine() > c.getLocation().getEndLine() and
    (
      later.(VariableAccess).getTarget() = d or
      later.(FieldAccess).getTarget() = d
    )
  )
}

from FunctionCall call, Function enclosing
where
  isErrnoReadAccessor(call.getTarget().getName()) and
  returnValueDiscarded(call) and
  enclosing = call.getEnclosingFunction() and
  // Make sure the call actually has an out-buffer argument and that
  // buffer is read after the call, otherwise the discarded return
  // value is benign.
  exists(Declaration d | outBufferLaterUsed(call, d))
select call,
  "Return value of " + call.getTarget().getName() +
    " is discarded; on failure the output buffer is left uninitialised " +
    "but is consumed later in '" + enclosing.getName() + "'."
