/**
 * @name Pointer dereferenced before NULL check
 * @description A function parameter pointer is dereferenced and then later
 *              checked for NULL within the same function. The NULL check
 *              indicates the developer believes NULL is possible, yet the
 *              earlier dereference would already crash on NULL input.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-mc-3
 */

import cpp

/** A NULL check on `p`: matches `!p`, `p == NULL`, `NULL == p`, `p == 0`. */
predicate isNullCheckOf(Expr check, Variable p) {
  exists(NotExpr ne |
    ne = check and
    ne.getOperand().(VariableAccess).getTarget() = p
  )
  or
  exists(EQExpr eq, Expr l, Expr r |
    eq = check and
    l = eq.getLeftOperand() and
    r = eq.getRightOperand() and
    (
      (l.(VariableAccess).getTarget() = p and r.getValue() = "0")
      or
      (r.(VariableAccess).getTarget() = p and l.getValue() = "0")
    )
  )
}

/** A dereference of `p`: `p->...`, `*p`, `&p->field`, etc. */
predicate isDerefOf(Expr deref, Variable p) {
  exists(PointerFieldAccess pfa |
    pfa = deref and
    pfa.getQualifier().(VariableAccess).getTarget() = p
  )
  or
  exists(PointerDereferenceExpr pd |
    pd = deref and
    pd.getOperand().(VariableAccess).getTarget() = p
  )
}

from Function f, Parameter p, Expr deref, Expr nullCheck
where
  p.getFunction() = f and
  p.getType() instanceof PointerType and
  isDerefOf(deref, p) and
  deref.getEnclosingFunction() = f and
  isNullCheckOf(nullCheck, p) and
  nullCheck.getEnclosingFunction() = f and
  // The dereference textually precedes (and thus dynamically may execute before)
  // the NULL check in the source.
  (
    deref.getLocation().getStartLine() < nullCheck.getLocation().getStartLine()
    or
    deref.getLocation().getStartLine() = nullCheck.getLocation().getStartLine() and
    deref.getLocation().getStartColumn() < nullCheck.getLocation().getStartColumn()
  ) and
  // The dereference must not itself be a NULL check or part of one.
  not deref.getParent*() = nullCheck
select deref,
  "Pointer '" + p.getName() + "' is dereferenced here, but later checked for NULL at line " +
    nullCheck.getLocation().getStartLine() + " in function '" + f.getName() + "'."
