/**
 * @name  rq3-c2-mc-3-rep3
 * @id    cpp/rq3/c2/mc-3-rep3
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 */
import cpp

predicate is_pointer_param(Parameter p) {
  p.getType().getUnspecifiedType() instanceof PointerType
}

predicate deref_of_param(Parameter p, Expr deref) {
  is_pointer_param(p) and
  (
    exists(PointerFieldAccess pfa |
      pfa = deref and pfa.getQualifier() = p.getAnAccess()
    )
    or
    exists(PointerDereferenceExpr pde |
      pde = deref and pde.getOperand() = p.getAnAccess()
    )
    or
    exists(ArrayExpr ae |
      ae = deref and ae.getArrayBase() = p.getAnAccess()
    )
  ) and
  deref.getEnclosingFunction() = p.getFunction()
}

predicate null_check_of_param(Parameter p, Expr check) {
  is_pointer_param(p) and
  check.getEnclosingFunction() = p.getFunction() and
  (
    exists(NotExpr ne |
      ne = check and ne.getOperand() = p.getAnAccess()
    )
    or
    exists(EqualityOperation eq |
      eq = check and
      eq.getAnOperand() = p.getAnAccess() and
      eq.getAnOperand().getValue() = "0"
    )
  )
}

predicate deref_before_check(Parameter p, Expr deref, Expr check) {
  deref_of_param(p, deref) and
  null_check_of_param(p, check) and
  (
    deref.getLocation().getStartLine() < check.getLocation().getStartLine()
    or
    (
      deref.getLocation().getStartLine() = check.getLocation().getStartLine() and
      deref.getLocation().getStartColumn() < check.getLocation().getStartColumn()
    )
  )
}

from Parameter p, Expr deref, Expr check
where deref_before_check(p, deref, check)
select deref, "Pointer parameter '" + p.getName() + "' is dereferenced here but checked for NULL later at line " + check.getLocation().getStartLine().toString() + "."
