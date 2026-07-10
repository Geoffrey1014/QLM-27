/**
 * @name  rq3-c2-mc-1-rep3
 * @id    cpp/rq3/c2/mc-1-rep3
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 */
import cpp

predicate isTargetCall(FunctionCall fc) {
  fc.getTarget().getName() = "regmap_bulk_read"
}

predicate isUncheckedCall(FunctionCall fc) {
  isTargetCall(fc) and
  // The call appears as an ExprStmt (its value is discarded), not used as an operand.
  exists(ExprStmt es | es.getExpr() = fc)
}

predicate outputBufferArg(FunctionCall fc, Expr buf) {
  isTargetCall(fc) and
  buf = fc.getArgument(1)
}

predicate bufferUsedAfter(FunctionCall fc, Expr buf) {
  outputBufferArg(fc, buf) and
  exists(Function f, Expr later |
    f = fc.getEnclosingFunction() and
    later.getEnclosingFunction() = f and
    later != buf and
    // crude "after" approximation by source-line ordering within the same function
    later.getLocation().getStartLine() > fc.getLocation().getStartLine() and
    (
      // Same variable access
      exists(Variable v |
        buf.(VariableAccess).getTarget() = v and
        later.(VariableAccess).getTarget() = v
      )
      or
      // Same field access on same qualifier variable
      exists(Field fld, Variable v |
        buf.(FieldAccess).getTarget() = fld and
        later.(FieldAccess).getTarget() = fld and
        buf.(FieldAccess).getQualifier().(VariableAccess).getTarget() = v and
        later.(FieldAccess).getQualifier().(VariableAccess).getTarget() = v
      )
    )
  )
}

predicate isBug(FunctionCall fc) {
  isUncheckedCall(fc) and
  exists(Expr buf | bufferUsedAfter(fc, buf))
}

from FunctionCall fc
where isBug(fc)
select fc, "Return value of regmap_bulk_read is not checked but the output buffer is subsequently used."
