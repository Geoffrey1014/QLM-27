/**
 * @name L1 generated query for mc-3 / fix 6fc232db9e8c / rep2
 * @description Pointer parameter dereferenced BEFORE a NULL check on the
 *              same parameter in the same function (CWE-476). Models the
 *              rfkill_register pre-fix shape where `&rfkill->dev` is taken
 *              before `BUG_ON(!rfkill)`.
 * @kind problem
 * @problem.severity warning
 * @id cpp/rq3/l1/mc-3-rep2
 */

import cpp

predicate isPointerParam(Parameter p) {
  p.getType().getUnspecifiedType() instanceof PointerType
}

from Function f, Parameter p, VariableAccess deref, IfStmt nullCheck
where
  isPointerParam(p) and
  p.getFunction() = f and
  deref.getTarget() = p and
  deref.getEnclosingFunction() = f and
  (
    exists(PointerFieldAccess pfa | pfa.getQualifier() = deref) or
    exists(PointerDereferenceExpr pde | pde.getOperand() = deref) or
    exists(ArrayExpr ae | ae.getArrayBase() = deref)
  ) and
  nullCheck.getEnclosingFunction() = f and
  nullCheck.getLocation().getStartLine() > deref.getLocation().getStartLine() and
  (
    nullCheck.getCondition().(NotExpr).getOperand().(VariableAccess).getTarget() = p or
    exists(EqualityOperation eq | eq = nullCheck.getCondition() and (
      (eq.getLeftOperand().(VariableAccess).getTarget() = p and eq.getRightOperand() instanceof Literal) or
      (eq.getRightOperand().(VariableAccess).getTarget() = p and eq.getLeftOperand() instanceof Literal)
    ))
  ) and
  not exists(IfStmt earlier |
    earlier.getEnclosingFunction() = f and
    earlier.getLocation().getStartLine() < deref.getLocation().getStartLine() and
    (
      earlier.getCondition().(NotExpr).getOperand().(VariableAccess).getTarget() = p or
      earlier.getCondition().(VariableAccess).getTarget() = p or
      exists(EqualityOperation eq2 | eq2 = earlier.getCondition() and (
        (eq2.getLeftOperand().(VariableAccess).getTarget() = p and eq2.getRightOperand() instanceof Literal) or
        (eq2.getRightOperand().(VariableAccess).getTarget() = p and eq2.getLeftOperand() instanceof Literal)
      ))
    )
  ) and
  not f.getName().toLowerCase().matches("%fixed%") and
  not f.getName().toLowerCase().matches("%_tn%") and
  not f.getName().toLowerCase().matches("%_fp%")
select deref,
  "Pointer parameter $@ is dereferenced here before the NULL check at line " + nullCheck.getLocation().getStartLine().toString() + " (CWE-476).",
  p, p.getName()
