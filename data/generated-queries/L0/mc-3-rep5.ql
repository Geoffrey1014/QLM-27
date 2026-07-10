/**
 * @name Dereference of pointer parameter before NULL check
 * @description Detects pointer parameters that are dereferenced (via field
 *              access or address-of a field) before a NULL check on the same
 *              parameter in the same function. Pattern derived from upstream
 *              commit 6fc232db9e8c ("rfkill: Fix incorrect check to avoid
 *              NULL pointer dereference").
 * @kind problem
 * @problem.severity warning
 * @id qlm/l0-mc3-missing-null-check
 * @tags reliability
 *       missing-check
 *       CWE-476
 */

import cpp

predicate isNullCheckOf(Expr check, Parameter p) {
  // shape 1: !p
  check.(NotExpr).getOperand().(VariableAccess).getTarget() = p
  or
  // shape 2: p == NULL or p == 0 (either order)
  exists(EqualityOperation eq | eq = check |
    eq.getAnOperand().(VariableAccess).getTarget() = p and
    (
      eq.getAnOperand() instanceof NullValue or
      eq.getAnOperand().getValue() = "0"
    )
  )
}

from Function f, Parameter p, VariableAccess derefUse, Expr nullCheck
where
  p = f.getAParameter() and
  p.getType().getUnspecifiedType() instanceof PointerType and
  derefUse.getTarget() = p and
  derefUse.getEnclosingFunction() = f and
  // deref shape: p->field  OR  &p->field
  (
    exists(PointerFieldAccess pfa | pfa.getQualifier() = derefUse)
    or
    exists(AddressOfExpr ao, PointerFieldAccess pfa2 |
      pfa2.getQualifier() = derefUse and ao.getOperand() = pfa2
    )
  ) and
  isNullCheckOf(nullCheck, p) and
  nullCheck.getEnclosingFunction() = f and
  derefUse.getLocation().getStartLine() < nullCheck.getLocation().getStartLine()
select derefUse,
  "Dereference of parameter '" + p.getName() +
  "' occurs before NULL check in function " + f.getName()
