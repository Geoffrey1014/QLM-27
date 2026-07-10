/**
 * @name Pointer dereferenced before NULL check
 * @description A pointer parameter is dereferenced before being checked for NULL
 *              in the same function. Any caller passing NULL will dereference
 *              NULL before the guard takes effect.
 * @kind problem
 * @problem.severity error
 * @id qlm/missing-check/deref-before-null-check
 * @tags correctness
 *       reliability
 *       security
 *       external/cwe/cwe-476
 */

import cpp

/* True iff p is declared as a pointer-typed parameter. */
predicate isParamPointer(Parameter p) {
  p.getType().getUnspecifiedType() instanceof PointerType
}

/* True iff va is a use of v that constitutes a pointer dereference. */
predicate isPointerDerefOf(VariableAccess va, Variable v) {
  va = v.getAnAccess() and
  (
    exists(PointerFieldAccess pfa | pfa.getQualifier() = va)
    or
    exists(PointerDereferenceExpr pde | pde.getOperand() = va)
    or
    exists(ArrayExpr ae | ae.getArrayBase() = va)
  )
}

/* True iff `check` is an expression that compares v to NULL/0. */
predicate isNullCheckOf(Expr check, Variable v) {
  exists(NotExpr ne | ne = check and ne.getOperand() = v.getAnAccess())
  or
  exists(EQExpr eq | eq = check and
    eq.getAnOperand() = v.getAnAccess() and
    eq.getAnOperand().getValue() = "0")
  or
  exists(NEExpr ne | ne = check and
    ne.getAnOperand() = v.getAnAccess() and
    ne.getAnOperand().getValue() = "0")
}

/* True iff `deref` is a deref of v that textually precedes a null check on v
 * in the same enclosing function. */
predicate derefBeforeNullCheck(VariableAccess deref, Expr check, Variable v) {
  isPointerDerefOf(deref, v) and
  isNullCheckOf(check, v) and
  deref.getEnclosingFunction() = check.getEnclosingFunction() and
  deref.getLocation().getStartLine() < check.getLocation().getStartLine()
}

from Function f, Parameter p, VariableAccess deref, Expr check
where
  isParamPointer(p) and
  p.getFunction() = f and
  derefBeforeNullCheck(deref, check, p)
select deref,
  "Pointer parameter '" + p.getName() +
  "' is dereferenced here before the NULL check at " +
  check.getLocation().toString() + " in function " + f.getName() + "."
