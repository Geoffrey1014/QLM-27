/**
 * @name  rq3-c2-mc-5-rep3
 * @id    cpp/rq3/c2/mc-5-rep3
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2: missing NULL check after devm_k*alloc.
 */
import cpp
import semmle.code.cpp.controlflow.Guards

predicate isDevmAllocCall(FunctionCall fc) {
  exists(Function f | f = fc.getTarget() |
    f.getName() = "devm_kcalloc" or
    f.getName() = "devm_kzalloc" or
    f.getName() = "devm_kmalloc" or
    f.getName() = "devm_kmalloc_array" or
    f.getName() = "devm_kzalloc_array"
  )
}

predicate storesToField(FunctionCall fc, Field f) {
  exists(Assignment a |
    a.getRValue() = fc and
    a.getLValue().(FieldAccess).getTarget() = f
  )
}

predicate derefsField(Expr e, Field f) {
  exists(FieldAccess fa |
    fa.getTarget() = f and
    (
      e.(PointerFieldAccess).getQualifier() = fa or
      e.(PointerDereferenceExpr).getOperand() = fa or
      e.(ArrayExpr).getArrayBase() = fa
    )
  )
}

predicate guardsFieldNotNull(GuardCondition g, Field f) {
  exists(FieldAccess fa | fa.getTarget() = f and fa.getParent*() = g)
}

predicate unguardedFieldDeref(FunctionCall fc, Expr deref, Field f) {
  isDevmAllocCall(fc) and
  storesToField(fc, f) and
  derefsField(deref, f) and
  fc.getEnclosingFunction() != deref.getEnclosingFunction() and
  not exists(GuardCondition g | guardsFieldNotNull(g, f))
}

from FunctionCall fc, Expr deref, Field f
where unguardedFieldDeref(fc, deref, f)
select fc, "Result of " + fc.getTarget().getName() + " stored in field " + f.getName() + " is dereferenced without NULL check (e.g. at $@).", deref, "this dereference"
