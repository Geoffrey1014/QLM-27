/**
 * @name Pointer parameter dereferenced before NULL check
 * @description A pointer parameter is dereferenced before being checked for NULL
 *              in the same function. Any caller passing NULL will dereference
 *              NULL before the guard takes effect.
 * @kind problem
 * @problem.severity error
 * @id qlm/missing-check/deref-before-null-check-l0
 * @tags correctness
 *       reliability
 *       security
 *       external/cwe/cwe-476
 */

import cpp

predicate derefBeforeNullCheck(VariableAccess deref, Expr check, Parameter p) {
  p.getType().getUnspecifiedType() instanceof PointerType and
  deref = p.getAnAccess() and
  (
    exists(PointerFieldAccess pfa | pfa.getQualifier() = deref)
    or
    exists(PointerDereferenceExpr pde | pde.getOperand() = deref)
    or
    exists(ArrayExpr ae | ae.getArrayBase() = deref)
  ) and
  (
    exists(NotExpr ne | ne = check and ne.getOperand() = p.getAnAccess())
    or
    exists(EQExpr eq |
      eq = check and
      eq.getAnOperand() = p.getAnAccess() and
      eq.getAnOperand().getValue() = "0"
    )
    or
    exists(NEExpr ne |
      ne = check and
      ne.getAnOperand() = p.getAnAccess() and
      ne.getAnOperand().getValue() = "0"
    )
  ) and
  deref.getEnclosingFunction() = check.getEnclosingFunction() and
  deref.getEnclosingFunction() = p.getFunction() and
  deref.getLocation().getStartLine() < check.getLocation().getStartLine()
}

from VariableAccess deref, Expr check, Parameter p
where derefBeforeNullCheck(deref, check, p)
select deref,
  "Pointer parameter '" + p.getName() +
  "' is dereferenced here before the NULL check (" + check.toString() +
  ") at " + check.getLocation().toString() +
  " in function " + deref.getEnclosingFunction().getName() + "."
