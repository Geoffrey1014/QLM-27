/**
 * @name Missing NULL check after allocation
 * @description Detects a call to a kernel allocator whose result is stored
 *              into a variable that is subsequently dereferenced without a
 *              NULL check in the same function.
 * @kind problem
 * @problem.severity warning
 * @id cpp/missing-null-check-after-alloc
 */

import cpp

predicate isAllocCall(FunctionCall fc) {
  fc.getTarget().getName() = [
    "devm_kcalloc", "devm_kzalloc", "devm_kmalloc",
    "kmalloc", "kzalloc", "kcalloc", "krealloc"
  ]
}

/** Any expression that syntactically "checks" e for NULL (or non-NULL). */
predicate isNullCheck(Expr e, Expr target) {
  // if (!target)
  e.(NotExpr).getOperand() = target
  or
  // if (target == 0 / NULL) or (0 == target)
  exists(EQExpr eq | eq = e |
    (eq.getLeftOperand() = target and eq.getRightOperand().getValue() = "0")
    or
    (eq.getRightOperand() = target and eq.getLeftOperand().getValue() = "0")
  )
  or
  // if (target != 0)
  exists(NEExpr ne | ne = e |
    (ne.getLeftOperand() = target and ne.getRightOperand().getValue() = "0")
    or
    (ne.getRightOperand() = target and ne.getLeftOperand().getValue() = "0")
  )
  or
  // if (target)  — bare truthiness of a pointer counts as a NULL check
  e = target and target.getType() instanceof PointerType
}

/** Any use of `target` that dereferences it (obviously unsafe if NULL). */
predicate isDeref(Expr use, Expr target) {
  // *p
  use.(PointerDereferenceExpr).getOperand() = target
  or
  // p->field
  exists(PointerFieldAccess pfa | pfa.getQualifier() = target and use = pfa)
  or
  // p[i]
  exists(ArrayExpr ae | ae.getArrayBase() = target and use = ae)
}

/** Function `f` contains a NULL check on some access of `v`. */
predicate hasNullCheckOn(Function f, Variable v) {
  exists(VariableAccess va, Expr check |
    va.getTarget() = v and
    va.getEnclosingFunction() = f and
    isNullCheck(check, va)
  )
}

from FunctionCall alloc, Variable v, VariableAccess deref, Expr derefExpr, Function f
where
  isAllocCall(alloc) and
  f = alloc.getEnclosingFunction() and
  // The allocation result is stored into some variable v (either a plain
  // local Variable or a Field target on a struct).
  exists(Assignment a |
    a.getRValue() = alloc and
    (
      a.getLValue().(VariableAccess).getTarget() = v
      or
      a.getLValue().(FieldAccess).getTarget() = v
    )
  ) and
  // A subsequent access of v is dereferenced inside the same function.
  deref.getTarget() = v and
  deref.getEnclosingFunction() = f and
  isDeref(derefExpr, deref) and
  // No NULL check on v anywhere in the function.
  not hasNullCheckOn(f, v)
select alloc,
  "Missing NULL check on '" + v.getName() +
    "' after allocation call to '" + alloc.getTarget().getName() +
    "' before dereference."
