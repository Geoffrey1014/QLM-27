/**
 * @name  rq3-c2-mc-3-rep1
 * @id    cpp/rq3/c2/mc-3-rep1
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 */
import cpp

predicate is_pointer_param(Parameter p) {
  p.getType().getUnspecifiedType() instanceof PointerType
}

predicate param_deref(Parameter p, Expr deref) {
  is_pointer_param(p) and
  deref.getEnclosingFunction() = p.getFunction() and
  (
    exists(PointerFieldAccess pfa | pfa = deref and pfa.getQualifier() = p.getAnAccess())
    or
    exists(PointerDereferenceExpr pde | pde = deref and pde.getOperand() = p.getAnAccess())
    or
    exists(ArrayExpr ae | ae = deref and ae.getArrayBase() = p.getAnAccess())
  )
}

predicate param_null_check(Parameter p, Expr check) {
  is_pointer_param(p) and
  check.getEnclosingFunction() = p.getFunction() and
  (
    exists(NotExpr ne | ne = check and ne.getOperand() = p.getAnAccess())
    or
    exists(EQExpr eq | eq = check and eq.getAnOperand() = p.getAnAccess() and eq.getAnOperand().getValue() = "0")
    or
    exists(NEExpr ne2 | ne2 = check and ne2.getAnOperand() = p.getAnAccess() and ne2.getAnOperand().getValue() = "0")
  )
}

predicate deref_not_preceded_by_check(Parameter p, Expr deref) {
  param_deref(p, deref) and
  not exists(Expr check |
    param_null_check(p, check) and
    (
      check.getLocation().getStartLine() < deref.getLocation().getStartLine()
      or
      (
        check.getLocation().getStartLine() = deref.getLocation().getStartLine() and
        check.getLocation().getStartColumn() < deref.getLocation().getStartColumn()
      )
    )
  )
}

from Parameter p, Expr deref, Expr check
where
  deref_not_preceded_by_check(p, deref) and
  param_null_check(p, check)
select deref,
  "Pointer parameter '" + p.getName() +
  "' is dereferenced here but a NULL check appears later at line " +
  check.getLocation().getStartLine().toString() + "."
