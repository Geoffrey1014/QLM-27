/**
 * @name C3 generated query for mc-3 / fix 6fc232db9e8c
 * @description Use of a pointer parameter BEFORE a NULL check on the same
 *              parameter -- classic use-before-null-check (CWE-476).
 *              Pattern: rfkill: Fix incorrect check to avoid NULL pointer
 *              dereference (net/rfkill/core.c, rfkill_register).
 * @kind problem
 * @problem.severity warning
 * @id cpp/rq3/c3/mc-3-rep3
 */

import cpp

predicate isPointerParam(Parameter p) {
  p.getType().getUnspecifiedType() instanceof PointerType
}

predicate derefOfParam(Parameter p, Expr derefSite) {
  isPointerParam(p) and
  (
    exists(PointerFieldAccess pfa |
      derefSite = pfa and
      pfa.getQualifier().(VariableAccess).getTarget() = p
    )
    or
    exists(PointerDereferenceExpr pde |
      derefSite = pde and
      pde.getOperand().(VariableAccess).getTarget() = p
    )
    or
    exists(AddressOfExpr aoe, PointerFieldAccess pfa2 |
      derefSite = aoe and
      aoe.getOperand() = pfa2 and
      pfa2.getQualifier().(VariableAccess).getTarget() = p
    )
  )
}

predicate nullCheckOnParam(Parameter p, Expr checkSite) {
  isPointerParam(p) and
  exists(VariableAccess va |
    va.getTarget() = p and
    va = checkSite.getAChild*()
  ) and
  (
    exists(IfStmt ifs | ifs.getCondition() = checkSite)
    or
    exists(ConditionalExpr ce | ce.getCondition() = checkSite)
    or
    exists(LogicalAndExpr lae | lae.getAnOperand() = checkSite)
    or
    exists(LogicalOrExpr loe | loe.getAnOperand() = checkSite)
  )
}

predicate derefBeforeNullCheck(Parameter p, Expr derefSite, Expr checkSite) {
  derefOfParam(p, derefSite) and
  nullCheckOnParam(p, checkSite) and
  derefSite.getEnclosingFunction() = checkSite.getEnclosingFunction() and
  derefSite.getLocation().getStartLine() < checkSite.getLocation().getStartLine()
}

predicate isInFixedOrFpFunction(Function f) {
  f.getName().toLowerCase().matches("%fixed%") or
  f.getName().toLowerCase().matches("fp\\_%") or
  f.getName().toLowerCase().matches("%\\_fp\\_%") or
  f.getName().toLowerCase().matches("%\\_tn%")
}

from Parameter p, Expr d, Expr c
where
  derefBeforeNullCheck(p, d, c) and
  not isInFixedOrFpFunction(d.getEnclosingFunction())
select d,
  "Pointer parameter '" + p.getName() +
  "' is dereferenced at line " + d.getLocation().getStartLine() +
  " BEFORE the NULL-check at line " + c.getLocation().getStartLine() +
  " -- use-before-null-check (CWE-476)"
