/**
 * @name Missing NULL check of devm_-family allocator stored in struct member
 * @description Detects calls to devm_kcalloc / devm_kzalloc / devm_kmalloc_array
 *              whose return is assigned to a struct field (`obj->field = devm_...`)
 *              and where the same struct field is later dereferenced (array index,
 *              `*ptr`, or `ptr->member`) without any intervening NULL-check guard
 *              (IfStmt on the field, `field &&`/`!field ||`/ternary on the field).
 *              Pattern derived from upstream commit d6cb77228e3a
 *              ("pinctrl: baytrail: Fix potential NULL pointer dereference").
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3/c3/missing-check-devm-alloc-null
 * @tags reliability
 *       missing-check
 *       cwe-476
 */

import cpp

/* P1: devm_-family allocator that may return NULL on OOM. */
predicate isDevmAllocCall(FunctionCall fc) {
  exists(string n | n = fc.getTarget().getName() |
    n = "devm_kcalloc" or n = "devm_kzalloc" or n = "devm_kmalloc_array"
  )
}

/* P2: allocator result is assigned to a struct field (qualified field access),
 * i.e. `obj->field = devm_alloc(...)`. */
predicate assignsToStructFieldOnVg(FunctionCall fc, FieldAccess fa) {
  isDevmAllocCall(fc) and
  exists(AssignExpr a | a.getRValue() = fc and fa = a.getLValue()) and
  exists(fa.getQualifier())
}

/* Helper: `fa` is being used as a dereference base (ptr[i], *ptr, ptr->m).
 * Excludes sizeof contexts (unevaluated). */
predicate isDereferencedHere(FieldAccess fa) {
  (
    exists(ArrayExpr ae | ae.getArrayBase() = fa) or
    exists(PointerDereferenceExpr pd | pd.getOperand() = fa) or
    exists(PointerFieldAccess pfa | pfa.getQualifier() = fa)
  ) and
  not exists(SizeofOperator s | fa.getParent+() = s)
}

/* P3: SOME later FieldAccess on the same field is dereferenced without
 * an intervening NULL-check guard (IfStmt, &&, !||, ?:). */
predicate fieldUnconditionallyDereferenced(FieldAccess fa) {
  exists(FieldAccess use, Function fn |
    fn = fa.getEnclosingFunction() and
    use.getEnclosingFunction() = fn and
    use.getTarget() = fa.getTarget() and
    use.getLocation().getStartLine() > fa.getLocation().getStartLine() and
    isDereferencedHere(use) and
    /* not on the right of an `&&` whose left mentions the same field */
    not exists(LogicalAndExpr land, FieldAccess g |
      use = land.getRightOperand().getAChild*() and
      g = land.getLeftOperand().getAChild*() and
      g.getTarget() = fa.getTarget()
    ) and
    /* not on the right of an `||` whose left is `!field` */
    not exists(LogicalOrExpr lor, NotExpr ne, FieldAccess g3 |
      use = lor.getRightOperand().getAChild*() and
      ne = lor.getLeftOperand() and
      g3 = ne.getOperand().getAChild*() and
      g3.getTarget() = fa.getTarget()
    ) and
    /* not in the then-branch of a ternary whose condition mentions the field */
    not exists(ConditionalExpr ce, FieldAccess g4 |
      use = ce.getThen().getAChild*() and
      g4 = ce.getCondition().getAChild*() and
      g4.getTarget() = fa.getTarget()
    ) and
    /* not inside an IfStmt body whose condition mentions the field */
    not exists(IfStmt ig, FieldAccess g5 |
      ig.getEnclosingFunction() = fn and
      g5 = ig.getCondition().getAChild*() and
      g5.getTarget() = fa.getTarget() and
      use.getParent+() = ig.getThen()
    )
  )
}

from FunctionCall fc, FieldAccess fa
where assignsToStructFieldOnVg(fc, fa) and
      fieldUnconditionallyDereferenced(fa)
select fc,
       "Result of " + fc.getTarget().getName() +
       " stored into ->" + fa.getTarget().getName() +
       " with no NULL check before downstream dereference " +
       "(missing-check NULL pointer dereference) in " +
       fc.getEnclosingFunction().getName()
