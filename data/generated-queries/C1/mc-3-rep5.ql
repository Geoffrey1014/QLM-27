/**
 * @name Pointer dereferenced before NULL check
 * @description A pointer parameter is dereferenced (via field access or
 *              direct dereference) and then later checked against NULL in
 *              the same function. The NULL check is too late: if the
 *              pointer is NULL, the earlier dereference is undefined
 *              behavior.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-mc-3
 */

import cpp

/** Holds if `e` syntactically dereferences `v` (`*v`, `v->...`, or `&v->...`). */
predicate dereferences(Expr e, Variable v) {
  exists(PointerFieldAccess pfa |
    pfa = e and
    pfa.getQualifier().(VariableAccess).getTarget() = v
  )
  or
  exists(PointerDereferenceExpr d |
    d = e and
    d.getOperand().(VariableAccess).getTarget() = v
  )
  or
  // &v->field counts as a dereference of v
  exists(AddressOfExpr aoe, PointerFieldAccess pfa |
    aoe = e and
    pfa = aoe.getOperand() and
    pfa.getQualifier().(VariableAccess).getTarget() = v
  )
}

/** Holds if `e` is (or contains) a NULL check on variable `v`. */
predicate isNullCheckOn(Expr e, Variable v) {
  // `!v`
  exists(NotExpr ne |
    ne = e and
    ne.getOperand().(VariableAccess).getTarget() = v
  )
  or
  // `v == NULL` or `NULL == v` or `v != NULL` or `NULL != v`
  exists(EqualityOperation eq |
    eq = e and
    (
      eq.getLeftOperand().(VariableAccess).getTarget() = v and
      eq.getRightOperand().getValue() = "0"
      or
      eq.getRightOperand().(VariableAccess).getTarget() = v and
      eq.getLeftOperand().getValue() = "0"
    )
  )
}

from Function fn, Parameter p, Expr deref, IfStmt nullCheck, Expr cond
where
  // The parameter must be a pointer type.
  p.getFunction() = fn and
  p.getType().getUnspecifiedType() instanceof PointerType and
  // A dereference of the parameter occurs inside the function.
  dereferences(deref, p) and
  deref.getEnclosingFunction() = fn and
  // A NULL check on the same parameter exists in the function.
  nullCheck.getEnclosingFunction() = fn and
  cond = nullCheck.getCondition().getAChild*() and
  isNullCheckOn(cond, p) and
  // The dereference textually precedes the NULL check.
  deref.getLocation().getStartLine() < nullCheck.getLocation().getStartLine() and
  // Both live in the same file.
  deref.getLocation().getFile() = nullCheck.getLocation().getFile() and
  // Exclude assignments where the dereference's value is unused
  // (we still want to flag any read).
  not deref.isUnevaluated()
select deref,
  "Pointer parameter '" + p.getName() +
    "' is dereferenced here at line " + deref.getLocation().getStartLine() +
    " but a NULL check on it appears later at line " +
    nullCheck.getLocation().getStartLine() + " in function '" + fn.getName() + "'."
