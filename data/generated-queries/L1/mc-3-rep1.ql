/**
 * @name Pointer parameter dereferenced before NULL check
 * @description A pointer function parameter is dereferenced (via -> or *)
 *              on a source line that precedes an in-function NULL check
 *              (`!p` or `p == 0`) of the same parameter. This is the
 *              rfkill_register-style bug: `struct device *dev = &rfkill->dev;`
 *              executed before `BUG_ON(!rfkill)`.
 * @kind problem
 * @problem.severity warning
 * @id qlm/mc3-deref-before-null-check
 * @tags correctness reliability
 */
import cpp

predicate derefBeforeNullCheck(Parameter p, Expr deref, Expr nullCheck) {
  p.getType() instanceof PointerType and
  deref.getEnclosingFunction() = p.getFunction() and
  (
    deref.(PointerFieldAccess).getQualifier() = p.getAnAccess() or
    deref.(PointerDereferenceExpr).getOperand() = p.getAnAccess()
  ) and
  nullCheck.getEnclosingFunction() = p.getFunction() and
  (
    exists(EqualityOperation eq |
      eq = nullCheck and
      eq.getAnOperand() = p.getAnAccess() and
      eq.getAnOperand() instanceof NullValue
    )
    or
    exists(NotExpr n |
      n = nullCheck and
      n.getOperand() = p.getAnAccess()
    )
  ) and
  deref.getLocation().getStartLine() < nullCheck.getLocation().getStartLine()
}

from Parameter p, Expr deref, Expr nullCheck
where derefBeforeNullCheck(p, deref, nullCheck)
select deref,
  "Pointer parameter '" + p.getName() +
  "' is dereferenced before NULL check at $@.",
  nullCheck, nullCheck.toString()
