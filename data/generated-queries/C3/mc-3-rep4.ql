/**
 * @name C3 generated query for mc-3 / fix 6fc232db9e8c / rep4
 * @description Use-before-null-check: a pointer parameter is dereferenced
 *              earlier in the function than its NULL-check, so the check
 *              is too late to prevent a NULL pointer dereference (CWE-476).
 * @kind problem
 * @problem.severity warning
 * @id cpp/rq3/c3/mc-3-rep4
 */

import cpp

/* True iff `check` is a null-test on variable `v`
   (one of: `!v`, `v == 0/NULL`, `v != 0/NULL`). */
predicate isNullCheckOf(Expr check, Variable v) {
  exists(VariableAccess va |
    check.getAChild*() = va and va.getTarget() = v
  ) and
  (
    exists(NotExpr ne | ne = check and ne.getOperand().(VariableAccess).getTarget() = v)
    or
    exists(EQExpr eq | eq = check and
      eq.getAnOperand().(VariableAccess).getTarget() = v and
      eq.getAnOperand().getValue().toInt() = 0)
    or
    exists(NEExpr ne2 | ne2 = check and
      ne2.getAnOperand().(VariableAccess).getTarget() = v and
      ne2.getAnOperand().getValue().toInt() = 0)
  )
}

/* True iff `deref` dereferences variable `v` (PointerFieldAccess
   `v->field`, AddressOfExpr on a PointerFieldAccess `&v->field`,
   or PointerDereferenceExpr `*v`). */
predicate isDerefOf(Expr deref, Variable v) {
  exists(PointerFieldAccess pfa |
    pfa = deref and pfa.getQualifier().(VariableAccess).getTarget() = v
  )
  or
  exists(AddressOfExpr aoe, PointerFieldAccess pfa |
    aoe = deref and aoe.getOperand() = pfa and
    pfa.getQualifier().(VariableAccess).getTarget() = v
  )
  or
  exists(PointerDereferenceExpr pde |
    pde = deref and pde.getOperand().(VariableAccess).getTarget() = v
  )
}

/* The bug pattern: a pointer parameter `p` of function `f` is
   dereferenced at `deref` BEFORE being null-checked at `check`. */
predicate derefBeforeCheck(Function f, Parameter p, Expr deref, Expr check) {
  p = f.getAParameter() and
  p.getType().getUnspecifiedType() instanceof PointerType and
  isDerefOf(deref, p) and
  isNullCheckOf(check, p) and
  deref.getEnclosingFunction() = f and
  check.getEnclosingFunction() = f and
  deref.getLocation().getStartLine() < check.getLocation().getStartLine()
}

from Function f, Parameter p, Expr deref, Expr check
where derefBeforeCheck(f, p, deref, check)
select deref,
  "Pointer parameter '" + p.getName() + "' is dereferenced at line " +
    deref.getLocation().getStartLine().toString() +
    " before being null-checked at line " +
    check.getLocation().getStartLine().toString() +
    " in function '" + f.getName() +
    "' (CWE-476: NULL pointer dereference; the check is too late)."
