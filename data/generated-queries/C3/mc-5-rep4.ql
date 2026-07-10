/**
 * @name Missing NULL check after allocation
 * @description Result of an allocator (kzalloc/devm_kcalloc family) is
 *              dereferenced without being NULL-checked first. CWE-476.
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3/c3/missing-null-check-mc-5-rep4
 */

import cpp

predicate isAllocCall(FunctionCall fc) {
  fc.getTarget().getName() in [
    "devm_kcalloc", "devm_kzalloc", "devm_kmalloc", "devm_kmalloc_array",
    "kzalloc", "kmalloc", "kcalloc", "kmalloc_array",
    "vmalloc", "vzalloc"
  ]
}

Expr allocResultDest(FunctionCall fc) {
  isAllocCall(fc) and
  (
    result = fc.getParent().(AssignExpr).getLValue()
    or
    result.(VariableAccess).getTarget() = fc.getParent().(Initializer).getDeclaration()
  )
}

predicate hasNullCheckOn(FunctionCall fc, Expr dest) {
  dest = allocResultDest(fc) and
  exists(Expr cmp |
    cmp.getEnclosingFunction() = fc.getEnclosingFunction() and
    (
      cmp.(EqualityOperation).getAnOperand().toString() = dest.toString()
      or
      cmp.(NotExpr).getOperand().toString() = dest.toString()
    )
  )
}

predicate inSizeof(Expr e) {
  exists(SizeofOperator s | e = s.getAChild*())
}

predicate derefBeforeCheck(FunctionCall fc, Expr dest) {
  dest = allocResultDest(fc) and
  not hasNullCheckOn(fc, dest) and
  exists(Expr deref |
    deref.getEnclosingFunction() = fc.getEnclosingFunction() and
    deref != dest and
    not inSizeof(deref) and
    deref.getLocation().getStartLine() > fc.getLocation().getStartLine() and
    (
      deref.(PointerFieldAccess).getQualifier().toString() = dest.toString()
      or
      deref.(ArrayExpr).getArrayBase().toString() = dest.toString()
      or
      deref.(PointerDereferenceExpr).getOperand().toString() = dest.toString()
    )
  )
}

from FunctionCall fc, Expr dest
where
  isAllocCall(fc) and
  dest = allocResultDest(fc) and
  derefBeforeCheck(fc, dest)
select fc,
  "Result of " + fc.getTarget().getName() +
  " used without NULL check in " + fc.getEnclosingFunction().getName()
