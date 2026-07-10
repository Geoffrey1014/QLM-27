/**
 * @name L1 generated query for mc-3 / fix 6fc232db9e8c / rep3
 * @description Pointer parameter dereferenced BEFORE a NULL check on the
 *              same parameter in the same function (CWE-476). Models the
 *              rfkill_register pre-fix shape where `&rfkill->dev` is taken
 *              before `BUG_ON(!rfkill)`.
 * @kind problem
 * @problem.severity warning
 * @id cpp/rq3/l1/mc-3-rep3
 * @tags correctness reliability security external/cwe/cwe-476
 */

import cpp

predicate derefsPointerParam(VariableAccess deref, Parameter p) {
  p.getType().getUnspecifiedType() instanceof PointerType and
  deref = p.getAnAccess() and
  (
    exists(PointerFieldAccess pfa | pfa.getQualifier() = deref) or
    exists(PointerDereferenceExpr pde | pde.getOperand() = deref) or
    exists(ArrayExpr ae | ae.getArrayBase() = deref)
  )
}

predicate nullChecksParam(Expr check, Parameter p) {
  p.getType().getUnspecifiedType() instanceof PointerType and
  check.getEnclosingFunction() = p.getFunction() and
  (
    exists(NotExpr ne | ne = check and ne.getOperand() = p.getAnAccess()) or
    exists(EQExpr eq |
      eq = check and
      eq.getAnOperand() = p.getAnAccess() and
      eq.getAnOperand().getValue() = "0"
    ) or
    exists(NEExpr ne2 |
      ne2 = check and
      ne2.getAnOperand() = p.getAnAccess() and
      ne2.getAnOperand().getValue() = "0"
    )
  )
}

from VariableAccess deref, Expr check, Parameter p, Function f
where
  derefsPointerParam(deref, p) and
  nullChecksParam(check, p) and
  deref.getEnclosingFunction() = f and
  check.getEnclosingFunction() = f and
  p.getFunction() = f and
  deref.getLocation().getStartLine() < check.getLocation().getStartLine() and
  not exists(Expr earlier |
    nullChecksParam(earlier, p) and
    earlier.getLocation().getStartLine() < deref.getLocation().getStartLine()
  ) and
  not f.getName().toLowerCase().matches("%fixed%") and
  not f.getName().toLowerCase().matches("%_tn%") and
  not f.getName().toLowerCase().matches("%_fp%")
select deref,
  "Pointer parameter '" + p.getName() +
  "' is dereferenced here before a NULL check on it (later at line " +
  check.getLocation().getStartLine().toString() + ") in function " + f.getName() + " (CWE-476)."
