/**
 * @name  rq3-c2-mc-3-rep5
 * @id    cpp/rq3/c2/mc-3-rep5
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 */
import cpp

predicate is_pointer_param(Parameter p) {
  p.getUnderlyingType() instanceof PointerType
}

predicate param_dereferenced_at(Parameter p, Expr deref) {
  is_pointer_param(p) and
  deref.getEnclosingFunction() = p.getFunction() and
  (
    exists(PointerFieldAccess pfa |
      deref = pfa and pfa.getQualifier() = p.getAnAccess()
    )
    or
    exists(PointerDereferenceExpr pde |
      deref = pde and pde.getOperand() = p.getAnAccess()
    )
    or
    exists(ArrayExpr ae |
      deref = ae and ae.getArrayBase() = p.getAnAccess()
    )
  )
}

predicate param_null_checked_at(Parameter p, Expr check) {
  is_pointer_param(p) and
  check.getEnclosingFunction() = p.getFunction() and
  (
    exists(NotExpr ne |
      check = ne and ne.getOperand() = p.getAnAccess()
    )
    or
    exists(EqualityOperation eq |
      check = eq and
      eq.getAnOperand() = p.getAnAccess() and
      eq.getAnOperand().getValue() = "0"
    )
    or
    exists(FunctionCall fc |
      check = fc and
      (fc.getTarget().hasName("IS_ERR") or fc.getTarget().hasName("IS_ERR_OR_NULL")) and
      fc.getArgument(0) = p.getAnAccess()
    )
  )
}

predicate deref_before_null_check(Parameter p, Expr deref, Expr check) {
  param_dereferenced_at(p, deref) and
  param_null_checked_at(p, check) and
  deref.getFile() = check.getFile() and
  (
    deref.getLocation().getStartLine() < check.getLocation().getStartLine()
    or
    deref.getLocation().getStartLine() = check.getLocation().getStartLine() and
    deref.getLocation().getStartColumn() < check.getLocation().getStartColumn()
  )
}

from Parameter p, Expr deref, Expr check
where deref_before_null_check(p, deref, check)
select deref,
  "Pointer parameter '" + p.getName() + "' is dereferenced before NULL check at line "
    + check.getLocation().getStartLine().toString() + "."
