/**
 * @name Missing NULL check: pointer parameter dereferenced before being checked against NULL
 * @description A pointer parameter is dereferenced (via member access, array index, or
 *              address-of-a-field) before a subsequent NULL check on that same pointer
 *              parameter, indicating the check is too late: a NULL caller has already
 *              caused undefined behavior at the earlier deref.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-mc-3
 */

import cpp

/** A NULL test on `p`: `!p`, `p == 0`, `0 == p`, `p == NULL`, etc. */
predicate isNullCheckOn(Expr e, Parameter p) {
  // !p
  exists(NotExpr n |
    n = e and
    n.getOperand() = p.getAnAccess()
  )
  or
  // p == 0  or  0 == p
  exists(EQExpr eq, Expr z |
    eq = e and
    (
      (eq.getLeftOperand() = p.getAnAccess() and z = eq.getRightOperand())
      or
      (eq.getRightOperand() = p.getAnAccess() and z = eq.getLeftOperand())
    ) and
    z.getValue() = "0"
  )
}

/** Any statement that branches on a NULL check of `p` (covers `if (!p)`, `BUG_ON(!p)`
 *  via the contained if-stmt, etc.). */
predicate stmtChecksNull(Stmt s, Parameter p) {
  exists(IfStmt ifs |
    ifs = s and
    exists(Expr cond | cond = ifs.getCondition().getAChild*() or cond = ifs.getCondition() |
      isNullCheckOn(cond, p)
    )
  )
}

/** A dereference of pointer parameter `p`. */
predicate isDerefOf(Expr deref, Parameter p) {
  // p->field   (PointerFieldAccess uses p as its qualifier)
  exists(PointerFieldAccess pfa |
    pfa = deref and
    pfa.getQualifier() = p.getAnAccess()
  )
  or
  // *p
  exists(PointerDereferenceExpr pde |
    pde = deref and
    pde.getOperand() = p.getAnAccess()
  )
  or
  // p[i]
  exists(ArrayExpr ae |
    ae = deref and
    ae.getArrayBase() = p.getAnAccess()
  )
}

from Function f, Parameter p, Expr deref, Stmt checkStmt
where
  p.getFunction() = f and
  p.getType().getUnspecifiedType() instanceof PointerType and
  // dereference inside the function body
  isDerefOf(deref, p) and
  deref.getEnclosingFunction() = f and
  // a NULL check on the SAME parameter inside the same function
  stmtChecksNull(checkStmt, p) and
  checkStmt.getEnclosingFunction() = f and
  // the deref happens before the check (textually within the function)
  deref.getLocation().getStartLine() < checkStmt.getLocation().getStartLine() and
  // and on every control-flow path from function entry the deref reaches the check
  // (kept lightweight: require CFG successor relation)
  deref.getASuccessor+() = checkStmt and
  // the deref is NOT itself inside the body of another null check on p (avoid
  // matching the deref that is guarded by an earlier check)
  not exists(IfStmt guard |
    guard.getEnclosingFunction() = f and
    isNullCheckOn(guard.getCondition().getAChild*(), p) and
    guard.getLocation().getStartLine() < deref.getLocation().getStartLine() and
    deref.getEnclosingStmt().getParentStmt*() = guard.getThen()
  )
select deref,
  "Pointer parameter '" + p.getName() +
    "' is dereferenced here before being checked for NULL at $@.",
  checkStmt, "later NULL check"
