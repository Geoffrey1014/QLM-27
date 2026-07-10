/**
 * @name Dereference-before-NULL-check of pointer parameter
 * @description A pointer parameter is dereferenced before being checked
 *              against NULL inside the same function. The NULL check is
 *              effectively useless and the prior dereference may crash
 *              when the caller passes NULL.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-mc-3
 */

import cpp

/**
 * Holds if `e` is a NULL-ish test of pointer expression `p`:
 * forms like `!p`, `p == NULL`, `p == 0`, `NULL == p`, `0 == p`,
 * or symmetric `!= 0 / != NULL`.
 */
predicate isNullCheckOf(Expr e, Expr p) {
  // !p
  exists(NotExpr n |
    n = e and
    n.getOperand() = p and
    p.getType().getUnspecifiedType() instanceof PointerType
  )
  or
  // p == 0 / p == NULL / 0 == p / NULL == p / p != 0 / etc.
  exists(EqualityOperation eq, Expr lhs, Expr rhs |
    eq = e and
    lhs = eq.getLeftOperand() and
    rhs = eq.getRightOperand() and
    (
      (lhs = p and rhs.getValue().toInt() = 0) or
      (rhs = p and lhs.getValue().toInt() = 0)
    ) and
    p.getType().getUnspecifiedType() instanceof PointerType
  )
}

/**
 * Holds if `acc` is an access that dereferences pointer parameter `param`:
 * `*p`, `p->field`, `p[i]`, or array-style.
 */
predicate isDerefOfParam(Expr acc, Parameter param) {
  // p->field
  exists(PointerFieldAccess pfa |
    pfa = acc and
    pfa.getQualifier() = param.getAnAccess()
  )
  or
  // *p
  exists(PointerDereferenceExpr d |
    d = acc and
    d.getOperand() = param.getAnAccess()
  )
  or
  // p[i]
  exists(ArrayExpr ae |
    ae = acc and
    ae.getArrayBase() = param.getAnAccess()
  )
}

from Function f, Parameter param, Expr deref, Expr nullCheck, Expr paramUseInCheck
where
  // param is a pointer parameter of f
  param = f.getAParameter() and
  param.getType().getUnspecifiedType() instanceof PointerType and
  // there is a dereference of param inside f
  isDerefOfParam(deref, param) and
  deref.getEnclosingFunction() = f and
  // and there is a NULL check of param inside f
  paramUseInCheck = param.getAnAccess() and
  isNullCheckOf(nullCheck, paramUseInCheck) and
  nullCheck.getEnclosingFunction() = f and
  // the deref textually precedes the null check (same file, earlier line,
  // or earlier column on the same line)
  deref.getFile() = nullCheck.getFile() and
  (
    deref.getLocation().getStartLine() < nullCheck.getLocation().getStartLine()
    or
    (
      deref.getLocation().getStartLine() = nullCheck.getLocation().getStartLine() and
      deref.getLocation().getStartColumn() < nullCheck.getLocation().getStartColumn()
    )
  ) and
  // exclude derefs that are themselves inside the null check expression
  not nullCheck.getAChild*() = deref
select deref,
  "Pointer parameter '" + param.getName() +
    "' is dereferenced here before a later NULL check at line " +
    nullCheck.getLocation().getStartLine().toString() + "."
