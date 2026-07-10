/**
 * @name Pointer parameter dereferenced before NULL check
 * @description A pointer parameter is dereferenced in the same function before it
 *              is checked for NULL. Any caller passing NULL will trigger a NULL
 *              dereference before the guard takes effect (CWE-476).
 * @kind problem
 * @problem.severity error
 * @id qlm/l0-mc3-rep4-deref-before-null-check
 * @tags correctness
 *       reliability
 *       security
 *       external/cwe/cwe-476
 */

import cpp

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

from Function f, Parameter p, VariableAccess deref, Expr check
where
  p.getType().getUnspecifiedType() instanceof PointerType and
  p.getFunction() = f and
  isPointerDerefOf(deref, p) and
  deref.getEnclosingFunction() = f and
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
  check.getEnclosingFunction() = f and
  deref.getLocation().getStartLine() < check.getLocation().getStartLine()
select deref,
  "Pointer parameter '" + p.getName() + "' is dereferenced here before the NULL check at "
    + check.getLocation().toString() + " in function " + f.getName() + "."
