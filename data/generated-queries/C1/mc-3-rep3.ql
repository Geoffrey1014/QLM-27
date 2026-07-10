/**
 * @name Dereference before NULL check (missing-check)
 * @description A pointer parameter is dereferenced (e.g., field access via -> or
 *              address-of subfield) before being checked against NULL on a path
 *              where that NULL check exists later in the same function. This
 *              indicates that the NULL check happens too late and the
 *              dereference can crash on a NULL input.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-mc-3
 * @tags reliability
 *       correctness
 */

import cpp

/**
 * Holds if `e` is an expression that dereferences pointer-typed variable `v`
 * (either `v->field`, `&v->field`, or `*v`).
 */
predicate dereferencesPtr(Expr e, Variable v) {
  exists(VariableAccess va |
    va = e.(PointerFieldAccess).getQualifier() and
    va.getTarget() = v
  )
  or
  exists(VariableAccess va, PointerFieldAccess pfa |
    pfa = e.(AddressOfExpr).getOperand() and
    va = pfa.getQualifier() and
    va.getTarget() = v
  )
  or
  exists(VariableAccess va |
    va = e.(PointerDereferenceExpr).getOperand() and
    va.getTarget() = v
  )
}

/**
 * Holds if `cond` is a NULL-check on variable `v`, in either polarity
 * (`!v`, `v == NULL`, `NULL == v`, `v != NULL`, etc.).
 */
predicate nullCheckOn(Expr cond, Variable v) {
  exists(VariableAccess va | va.getTarget() = v |
    cond.(NotExpr).getOperand() = va
    or
    exists(EqualityOperation eq | eq = cond |
      eq.getAnOperand() = va and
      eq.getAnOperand().getValue() = "0"
    )
  )
}

from Function f, Parameter p, Expr deref, Expr nullCheck
where
  // The parameter is a pointer.
  p.getFunction() = f and
  p.getType() instanceof PointerType and
  // There is a dereference of the parameter inside the function.
  dereferencesPtr(deref, p) and
  deref.getEnclosingFunction() = f and
  // There is a NULL check on the same parameter, in the same function.
  nullCheckOn(nullCheck, p) and
  nullCheck.getEnclosingFunction() = f and
  // The NULL check is later in the source than the dereference.
  deref.getLocation().getStartLine() < nullCheck.getLocation().getStartLine() and
  // Same source file (defensive).
  deref.getLocation().getFile() = nullCheck.getLocation().getFile()
select deref,
  "Pointer parameter '" + p.getName() +
    "' is dereferenced here, but the NULL check on it at line " +
    nullCheck.getLocation().getStartLine().toString() + " happens later."
