/**
 * @name  rq3-c2-mc-5-rep2
 * @id    cpp/rq3/c2/mc-5-rep2
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects missing NULL check after allocator call (e.g. devm_kcalloc).
 */

import cpp

/** Holds if `fc` is a call to a memory allocator whose return value may be NULL. */
predicate isAllocCall(FunctionCall fc) {
  exists(string n | n = fc.getTarget().getName() |
    n = "devm_kcalloc" or
    n = "devm_kzalloc" or
    n = "devm_kmalloc" or
    n = "devm_kmalloc_array" or
    n = "kmalloc" or
    n = "kzalloc" or
    n = "kcalloc" or
    n = "kmalloc_array" or
    n = "vmalloc" or
    n = "vzalloc"
  )
}

/** Holds if the allocator call's return is stored into variable/field access `e`. */
predicate assignsToTarget(FunctionCall fc, Expr lhs) {
  exists(Assignment a |
    a.getRValue() = fc and
    a.getLValue() = lhs and
    isAllocCall(fc)
  )
  or
  exists(Variable v |
    v.getInitializer().getExpr() = fc and
    lhs = v.getAnAccess() and
    isAllocCall(fc)
  )
}

/** Holds if `e2` syntactically refers to the same storage location as `e1`
 *  (same variable, or same field on the same qualifier variable). */
predicate sameTarget(Expr e1, Expr e2) {
  exists(Variable v |
    e1 = v.getAnAccess() and e2 = v.getAnAccess()
  )
  or
  exists(FieldAccess fa1, FieldAccess fa2, Variable v |
    fa1 = e1 and fa2 = e2 and
    fa1.getTarget() = fa2.getTarget() and
    fa1.getQualifier().(VariableAccess).getTarget() = v and
    fa2.getQualifier().(VariableAccess).getTarget() = v
  )
}

/** Holds if a NULL check on a same-target expression appears in the same function
 *  after the allocator call `fc`. */
predicate hasNullCheckAfter(FunctionCall fc, Expr targetLhs) {
  exists(Expr checkExpr |
    sameTarget(targetLhs, checkExpr) and
    checkExpr.getEnclosingFunction() = fc.getEnclosingFunction() and
    (
      // if (!x)
      exists(NotExpr ne | ne.getOperand() = checkExpr)
      or
      // if (x == NULL) or (x == 0)
      exists(EQExpr eq |
        eq.getAnOperand() = checkExpr and
        eq.getAnOperand().getValue() = "0"
      )
      or
      // if (!x ...) used as condition implicitly
      exists(IfStmt is | is.getCondition() = checkExpr)
      or
      // unlikely(!x) / IS_ERR_OR_NULL(x) style
      exists(FunctionCall guard |
        guard.getAnArgument() = checkExpr and
        guard.getTarget().getName().regexpMatch("IS_ERR.*|unlikely|likely")
      )
    )
  )
}

/** Holds if the target storage `lhs` is later dereferenced (->, [], or *) in the
 *  same function as the alloc call. */
predicate isDereferencedAfter(FunctionCall fc, Expr lhs) {
  exists(Expr useExpr |
    sameTarget(lhs, useExpr) and
    useExpr.getEnclosingFunction() = fc.getEnclosingFunction() and
    (
      exists(PointerFieldAccess pfa | pfa.getQualifier() = useExpr)
      or
      exists(PointerDereferenceExpr pd | pd.getOperand() = useExpr)
      or
      exists(ArrayExpr ae | ae.getArrayBase() = useExpr)
    )
  )
}

from FunctionCall fc, Expr lhs
where
  isAllocCall(fc) and
  assignsToTarget(fc, lhs) and
  isDereferencedAfter(fc, lhs) and
  not hasNullCheckAfter(fc, lhs)
select fc,
  "Allocator return value assigned to target may be dereferenced without a NULL check."
