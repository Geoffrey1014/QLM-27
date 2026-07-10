/**
 * @name C3 generated query for mc-2 / fix 09acf29c8246
 * @description Missing NULL check after kzalloc — possible NULL pointer
 *              dereference (CWE-476). Detects k*alloc-family allocator calls
 *              whose result is stored and later dereferenced without an
 *              intervening NULL check.
 * @kind problem
 * @problem.severity warning
 * @id cpp/rq3/c3/mc-2-rep2
 */

import cpp

predicate isKzallocLike(FunctionCall fc) {
  fc.getTarget().getName() in [
    "kzalloc",
    "kmalloc",
    "kcalloc",
    "kmemdup",
    "kstrdup",
    "kstrndup",
    "vmalloc",
    "vzalloc",
    "kvmalloc",
    "kvzalloc"
  ]
}

Expr storedTarget(FunctionCall acquire) {
  exists(AssignExpr assign |
    assign.getRValue() = acquire and
    result = assign.getLValue()
  )
  or
  exists(Initializer init |
    init.getExpr() = acquire and
    result = init.getDeclaration().(LocalVariable).getAnAccess()
  )
}

predicate isNullLiteral(Expr e) {
  e instanceof Literal and e.getValue() = "0"
}

predicate exprMatchesTarget(Expr e, Expr target) {
  exists(VariableAccess va1, VariableAccess va2 |
    va1 = e and va2 = target and va1.getTarget() = va2.getTarget()
  )
  or
  exists(FieldAccess fa1, FieldAccess fa2 |
    fa1 = e and fa2 = target and fa1.getTarget() = fa2.getTarget()
  )
}

predicate isNullCompare(Expr e, Expr target) {
  exists(NotExpr ne | ne = e and exprMatchesTarget(ne.getOperand(), target))
  or
  exists(EQExpr eq | eq = e and
    (
      (exprMatchesTarget(eq.getLeftOperand(), target) and isNullLiteral(eq.getRightOperand()))
      or
      (exprMatchesTarget(eq.getRightOperand(), target) and isNullLiteral(eq.getLeftOperand()))
    )
  )
  or
  exists(NEExpr ne2 | ne2 = e and
    (
      (exprMatchesTarget(ne2.getLeftOperand(), target) and isNullLiteral(ne2.getRightOperand()))
      or
      (exprMatchesTarget(ne2.getRightOperand(), target) and isNullLiteral(ne2.getLeftOperand()))
    )
  )
}

predicate isNullCheckedBefore(FunctionCall acquire, Expr storedExpr) {
  exists(IfStmt ifStmt |
    ifStmt.getEnclosingFunction() = acquire.getEnclosingFunction() and
    exists(Expr cond | cond = ifStmt.getCondition().getAChild*() |
      isNullCompare(cond, storedExpr)
    )
  )
}

predicate isDereferencedAfter(FunctionCall acquire, Expr storedExpr) {
  exists(Expr useExpr |
    useExpr.getEnclosingFunction() = acquire.getEnclosingFunction() and
    exprMatchesTarget(useExpr, storedExpr) and
    useExpr != storedExpr and
    not useExpr.getParent() instanceof AssignExpr
  )
}

predicate isInFixedFunction(FunctionCall fc) {
  fc.getEnclosingFunction().getName().toLowerCase().matches("%fixed%")
}

from FunctionCall acquire, Expr storedExpr
where
  isKzallocLike(acquire) and
  storedExpr = storedTarget(acquire) and
  isDereferencedAfter(acquire, storedExpr) and
  not isNullCheckedBefore(acquire, storedExpr) and
  not isInFixedFunction(acquire)
select acquire,
  "Allocator '" + acquire.getTarget().getName() +
    "' result stored and dereferenced without a NULL check (possible NULL pointer dereference, CWE-476)"
