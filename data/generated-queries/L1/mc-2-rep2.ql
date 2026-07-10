/**
 * @name Missing NULL check after kzalloc-family allocation
 * @description Flags kzalloc/kmalloc/kcalloc calls whose result is stored
 *              into a variable that is later dereferenced (via field access)
 *              in the same function without any preceding IfStmt condition
 *              that references the variable.
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3/l1/mc-2-rep2
 */
import cpp

predicate isAllocCall(FunctionCall fc) {
  fc.getTarget().getName() = "kzalloc" or
  fc.getTarget().getName() = "kmalloc" or
  fc.getTarget().getName() = "kcalloc"
}

from FunctionCall alloc, AssignExpr assign, Variable v, VariableAccess derefUse
where
  isAllocCall(alloc) and
  assign.getRValue() = alloc and
  assign.getLValue().(VariableAccess).getTarget() = v and
  derefUse.getTarget() = v and
  derefUse.getEnclosingFunction() = alloc.getEnclosingFunction() and
  exists(FieldAccess fa | fa.getQualifier() = derefUse) and
  not exists(IfStmt ifs |
    ifs.getEnclosingFunction() = alloc.getEnclosingFunction() and
    ifs.getCondition().getAChild*().(VariableAccess).getTarget() = v)
select alloc,
  "Allocation result stored in $@ is dereferenced without a NULL check.",
  v, v.getName()
