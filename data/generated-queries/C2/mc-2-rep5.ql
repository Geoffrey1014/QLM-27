/**
 * @name  rq3-c2-mc-2-rep5
 * @id    cpp/rq3/c2/mc-2-rep5
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Missing NULL-check after allocation (kzalloc/kmalloc family).
 */
import cpp
import semmle.code.cpp.controlflow.Guards

predicate isAllocCall(FunctionCall fc) {
  fc.getTarget().getName() = ["kzalloc", "kmalloc", "kcalloc", "kmalloc_array",
                              "kzalloc_node", "kmalloc_node", "kvzalloc",
                              "kvmalloc", "vzalloc", "vmalloc", "devm_kzalloc",
                              "devm_kmalloc", "devm_kcalloc"]
}

predicate allocResultVar(FunctionCall fc, Variable v) {
  exists(Assignment a |
    a.getRValue() = fc and
    a.getLValue() = v.getAnAccess()
  )
  or
  exists(VariableDeclarationEntry vde |
    vde.getVariable() = v and
    vde.getDeclaration().(Variable).getInitializer().getExpr() = fc
  )
  or
  v.getInitializer().getExpr() = fc
}

predicate isNullCheckOf(GuardCondition g, Variable v) {
  exists(VariableAccess va | va = v.getAnAccess() |
    g = va or
    g.(NotExpr).getOperand() = va or
    exists(EqualityOperation eq | eq = g |
      eq.getAnOperand() = va and
      eq.getAnOperand().getValue() = "0"
    )
  )
}

predicate hasNullCheckAfter(FunctionCall fc, Variable v) {
  exists(GuardCondition g |
    isNullCheckOf(g, v) and
    fc.getASuccessor*() = g
  )
}

predicate isDerefOf(Expr e, Variable v) {
  exists(VariableAccess va | va = v.getAnAccess() |
    e.(PointerDereferenceExpr).getOperand() = va or
    e.(PointerFieldAccess).getQualifier() = va or
    e.(ArrayExpr).getArrayBase() = va
  )
}

predicate hasUnguardedDeref(FunctionCall fc, Variable v) {
  allocResultVar(fc, v) and
  exists(Expr d |
    isDerefOf(d, v) and
    fc.getASuccessor*() = d and
    not hasNullCheckAfter(fc, v)
  )
}

from FunctionCall fc, Variable v
where
  isAllocCall(fc) and
  allocResultVar(fc, v) and
  not hasNullCheckAfter(fc, v) and
  hasUnguardedDeref(fc, v)
select fc, "Allocation result assigned to $@ may be NULL but is dereferenced without a NULL check.", v, v.getName()
