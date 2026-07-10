/**
 * @name Unchecked return value of regmap_bulk_read in interrupt handler
 * @description Detects calls to regmap_bulk_read (and related error-returning
 *              read helpers) whose return value is discarded, where the data
 *              read into the output buffer is subsequently used. Such missing
 *              checks may cause the handler to act on stale/garbage data when
 *              the underlying I/O fails.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-mc-1
 */

import cpp

/**
 * Read-style APIs whose return value is an error code that callers must check
 * before relying on the data they wrote into an out-parameter.
 */
predicate isCheckedReadApi(string name) {
  name = "regmap_bulk_read" or
  name = "regmap_read" or
  name = "regmap_raw_read" or
  name = "regmap_noinc_read" or
  name = "regmap_multi_reg_read" or
  name = "regmap_fields_read"
}

/**
 * A call whose return value is discarded (i.e. it occurs as an ExprStmt and
 * is not bound to any variable, parameter, or other expression).
 */
predicate returnValueDiscarded(FunctionCall fc) {
  exists(ExprStmt es | es.getExpr() = fc) and
  not exists(Expr parent | parent.getAChild() = fc)
}

/**
 * Holds if `fc` writes data into an out-parameter expression `outArg`
 * (heuristic: the 3rd argument of the read API is the output buffer pointer).
 */
predicate writesToOutArg(FunctionCall fc, Expr outArg) {
  isCheckedReadApi(fc.getTarget().getName()) and
  outArg = fc.getArgument(2)
}

/**
 * A subsequent use of any sub-expression of `outArg` inside the same
 * enclosing function — indicating the discarded result has consequences.
 */
predicate hasLaterUseOfOutData(FunctionCall fc, Expr outArg) {
  exists(Function f, Expr later |
    fc.getEnclosingFunction() = f and
    later.getEnclosingFunction() = f and
    later.getLocation().getStartLine() > fc.getLocation().getStartLine() and
    (
      // a use of the variable / field that backed the out-arg
      exists(Variable v |
        outArg.(VariableAccess).getTarget() = v and
        later.(VariableAccess).getTarget() = v
      )
      or
      exists(Variable v |
        outArg.(AddressOfExpr).getOperand().(VariableAccess).getTarget() = v and
        later.(VariableAccess).getTarget() = v
      )
      or
      // a use of the receiver object (e.g. ts->conversion_data backed by ts)
      exists(Variable v |
        outArg.(FieldAccess).getQualifier().(VariableAccess).getTarget() = v and
        later.(VariableAccess).getTarget() = v
      )
      or
      exists(Variable v |
        outArg.(PointerFieldAccess).getQualifier().(VariableAccess).getTarget() = v and
        later.(VariableAccess).getTarget() = v
      )
    )
  )
}

from FunctionCall fc, Expr outArg
where
  isCheckedReadApi(fc.getTarget().getName()) and
  returnValueDiscarded(fc) and
  writesToOutArg(fc, outArg) and
  hasLaterUseOfOutData(fc, outArg)
select fc,
  "Return value of '" + fc.getTarget().getName() +
  "' is not checked before subsequent use of the data it wrote."
