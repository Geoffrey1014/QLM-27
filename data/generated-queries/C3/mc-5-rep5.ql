/**
 * @name JAWS RQ3 C3 mc-5-rep5: missing NULL check after devm_*-family
 *       allocation assigned to a struct member that is later dereferenced
 * @description Flags devm_kcalloc / devm_kzalloc / devm_kmalloc_array
 *              calls whose result is stored into a struct field and whose
 *              field is subsequently dereferenced in the same function
 *              without any NULL check on that field. Models the
 *              pinctrl-baytrail.c d6cb77228e3a bug pattern.
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3-c3-mc5-rep5
 */

import cpp

predicate isDevmAllocCall(FunctionCall fc) {
  exists(string n | n = fc.getTarget().getName() |
    n = "devm_kcalloc" or
    n = "devm_kzalloc" or
    n = "devm_kmalloc_array" or
    n = "devm_kmalloc" or
    n = "devm_kzalloc_array"
  )
}

predicate assignedToStructField(FunctionCall fc, FieldAccess fa) {
  exists(Assignment a | a.getRValue() = fc and a.getLValue() = fa)
}

predicate fieldDereferencedAfter(FieldAccess fa) {
  exists(FieldAccess use |
    use.getTarget() = fa.getTarget() and
    use != fa and
    use.getEnclosingFunction() = fa.getEnclosingFunction()
  |
    exists(PointerFieldAccess pfa | pfa.getQualifier() = use) or
    exists(ArrayExpr ae | ae.getArrayBase() = use) or
    exists(PointerDereferenceExpr pd | pd.getOperand() = use)
  )
}

predicate hasFieldNullCheck(FieldAccess fa) {
  exists(FieldAccess use, Expr cond |
    use.getTarget() = fa.getTarget() and
    use.getEnclosingFunction() = fa.getEnclosingFunction() and
    cond.getAChild*() = use
  |
    exists(IfStmt is | is.getCondition() = cond) or
    exists(ConditionalExpr ce | ce.getCondition() = cond) or
    exists(BinaryLogicalOperation blo |
      cond = blo.getLeftOperand() or cond = blo.getRightOperand() or
      blo.getAChild*() = use
    )
  )
}

from FunctionCall alloc, FieldAccess fa
where
  isDevmAllocCall(alloc) and
  assignedToStructField(alloc, fa) and
  fieldDereferencedAfter(fa) and
  not hasFieldNullCheck(fa)
select alloc,
  "devm-* allocation assigned to struct member '" + fa.getTarget().getName() +
    "' dereferenced without NULL check"
