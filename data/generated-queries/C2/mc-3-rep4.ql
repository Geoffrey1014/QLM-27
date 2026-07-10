/**
 * @name  rq3-c2-mc-3-rep4
 * @id    cpp/rq3/c2/mc-3-rep4
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects parameter pointers that are dereferenced before
 *              being checked for NULL within the same function.
 */
import cpp

/** Holds if `p` is a pointer-typed parameter. */
predicate is_pointer_param(Parameter p) {
  p.getType().getUnspecifiedType() instanceof PointerType
}

/**
 * Holds if `deref` is an expression in function `f` that dereferences
 * the parameter `p` (either via `*p`, `p->x`, or `&p->x`).
 */
predicate dereferences_param(Function f, Parameter p, Expr deref) {
  is_pointer_param(p) and
  p.getFunction() = f and
  (
    exists(PointerDereferenceExpr d |
      d = deref and
      d.getEnclosingFunction() = f and
      d.getOperand().(VariableAccess).getTarget() = p
    )
    or
    exists(FieldAccess fa |
      fa = deref and
      fa.getEnclosingFunction() = f and
      fa.getQualifier().(VariableAccess).getTarget() = p
    )
  )
}

/**
 * Holds if `check` is an expression in function `f` that NULL-checks
 * the parameter `p`. Recognises `!p`, `p == 0`, `p == NULL`, `p != NULL`.
 */
predicate null_check_of_param(Function f, Parameter p, Expr check) {
  is_pointer_param(p) and
  p.getFunction() = f and
  (
    exists(NotExpr n |
      n = check and
      n.getEnclosingFunction() = f and
      n.getOperand().(VariableAccess).getTarget() = p
    )
    or
    exists(EQExpr eq |
      eq = check and
      eq.getEnclosingFunction() = f and
      eq.getAnOperand().(VariableAccess).getTarget() = p and
      eq.getAnOperand().getValue() = "0"
    )
    or
    exists(NEExpr ne |
      ne = check and
      ne.getEnclosingFunction() = f and
      ne.getAnOperand().(VariableAccess).getTarget() = p and
      ne.getAnOperand().getValue() = "0"
    )
  )
}

/**
 * Holds if there is a dereference of `p` whose source location precedes
 * a NULL check of `p` in the same function `f`.
 */
predicate deref_before_null_check(Function f, Parameter p, Expr deref, Expr check) {
  dereferences_param(f, p, deref) and
  null_check_of_param(f, p, check) and
  (
    deref.getLocation().getStartLine() < check.getLocation().getStartLine()
    or
    (
      deref.getLocation().getStartLine() = check.getLocation().getStartLine() and
      deref.getLocation().getStartColumn() < check.getLocation().getStartColumn()
    )
  )
}

from Function f, Parameter p, Expr deref, Expr check
where deref_before_null_check(f, p, deref, check)
select deref,
  "Pointer parameter '" + p.getName() +
  "' is dereferenced here before being NULL-checked at line " +
  check.getLocation().getStartLine() + " in function '" + f.getName() + "'."
