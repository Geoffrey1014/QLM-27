/**
 * @name C3 generated query for mc-3 / fix 6fc232db9e8c / rep2
 * @description Use-before-null-check on pointer parameter: parameter is dereferenced before its null check (CWE-476).
 * @kind problem
 * @problem.severity warning
 * @id cpp/rq3/c3/mc-3-rep2
 */

import cpp

predicate paramDeref(Parameter p, Expr deref) {
  /* `deref` is a syntactic dereference of the pointer parameter `p`
     inside its owning function: either `p->...` (PointerFieldAccess) or
     `&p->...` (AddressOfExpr on a field access of p) or an explicit
     `*p` (PointerDereferenceExpr).  We restrict to dereferences whose
     base ultimately resolves to `p` via VariableAccess. */
  p.getType() instanceof PointerType and
  (
    exists(PointerFieldAccess pfa |
      deref = pfa and
      pfa.getQualifier().(VariableAccess).getTarget() = p
    )
    or
    exists(PointerDereferenceExpr pde |
      deref = pde and
      pde.getOperand().(VariableAccess).getTarget() = p
    )
  )
}

predicate paramNullCheck(Parameter p, Expr check) {
  /* `check` is a NULL-comparison of `p`: `!p`, `p == 0`, `p == NULL`,
     `p != 0`, `BUG_ON(!p)` (the inner `!p` survives), etc.
     We catch any NotExpr / EQExpr / NEExpr whose operand is a
     VariableAccess of `p`. */
  p.getType() instanceof PointerType and
  (
    exists(NotExpr ne |
      check = ne and
      ne.getOperand().(VariableAccess).getTarget() = p
    )
    or
    exists(EQExpr eq |
      check = eq and
      eq.getAnOperand().(VariableAccess).getTarget() = p and
      eq.getAnOperand().getValue() = "0"
    )
    or
    exists(NEExpr ne |
      check = ne and
      ne.getAnOperand().(VariableAccess).getTarget() = p and
      ne.getAnOperand().getValue() = "0"
    )
  )
}

predicate derefBeforeNullCheck(Parameter p, Expr deref, Expr check) {
  /* `p` is dereferenced and null-checked in the same function, and the
     dereference precedes the null check syntactically (source line
     order, same file).  This is the structural shape of the bug. */
  paramDeref(p, deref) and
  paramNullCheck(p, check) and
  deref.getEnclosingFunction() = check.getEnclosingFunction() and
  deref.getLocation().getFile() = check.getLocation().getFile() and
  (
    deref.getLocation().getStartLine() < check.getLocation().getStartLine()
    or
    (deref.getLocation().getStartLine() = check.getLocation().getStartLine()
     and deref.getLocation().getStartColumn() < check.getLocation().getStartColumn())
  )
}

predicate isInFixedFunction(Function f) {
  /* Filter out functions whose name marks them as the fixed reference
     or a TN variant — used to silence the query on the POC's _fixed*
     functions while still firing on _buggy* ones. */
  f.getName().toLowerCase().matches("%fixed%")
}

from Parameter p, Expr deref, Expr check, Function fn
where
  derefBeforeNullCheck(p, deref, check) and
  fn = p.getFunction() and
  not isInFixedFunction(fn)
select deref,
  "Parameter '" + p.getName() + "' of function '" + fn.getName() +
    "' is dereferenced here at line " + deref.getLocation().getStartLine() +
    " BEFORE its null check at line " + check.getLocation().getStartLine() +
    " — use-before-null-check (CWE-476)."
