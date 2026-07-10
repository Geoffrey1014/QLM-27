/**
 * @name Pointer parameter dereferenced before NULL check
 * @description A pointer function parameter is dereferenced (via ->, *, or [])
 *              on a source line that precedes an in-function NULL check
 *              (`!p`, `p == 0`, or `p != 0`) of the same parameter. This is
 *              the rfkill_register-style bug: `struct device *dev = &rfkill->dev;`
 *              executed before `BUG_ON(!rfkill)` (CWE-476).
 * @kind problem
 * @problem.severity error
 * @id qlm/l1-mc3-rep4-deref-before-null-check
 * @tags correctness
 *       reliability
 *       security
 *       external/cwe/cwe-476
 */

import cpp

predicate isPointerDerefOfParam(Expr deref, Parameter p) {
  p.getType().getUnspecifiedType() instanceof PointerType and
  deref.getEnclosingFunction() = p.getFunction() and
  (
    deref.(PointerFieldAccess).getQualifier() = p.getAnAccess()
    or
    deref.(PointerDereferenceExpr).getOperand() = p.getAnAccess()
    or
    deref.(ArrayExpr).getArrayBase() = p.getAnAccess()
  )
}

predicate isNullCheckOfParam(Expr check, Parameter p) {
  check.getEnclosingFunction() = p.getFunction() and
  (
    exists(NotExpr n | n = check and n.getOperand() = p.getAnAccess())
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
  )
}

from Function f, Parameter p, Expr deref, Expr check
where
  p.getFunction() = f and
  isPointerDerefOfParam(deref, p) and
  isNullCheckOfParam(check, p) and
  deref.getLocation().getStartLine() < check.getLocation().getStartLine()
select deref,
  "Pointer parameter '" + p.getName() + "' is dereferenced here before the NULL check at "
    + check.getLocation().toString() + " in function " + f.getName() + "."
