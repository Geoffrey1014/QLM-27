/**
 * @name L0 generated query for mc-2 / fix 09acf29c8246 / rep5
 * @description Missing NULL check after kernel allocation (kzalloc / kmalloc /
 *              kcalloc / kmalloc_array / kzalloc_node / vmalloc / vzalloc):
 *              the allocation result is dereferenced in the enclosing function
 *              without an intervening NULL check on the result variable
 *              (CWE-476).
 * @kind problem
 * @problem.severity warning
 * @id cpp/rq3/l0/mc-2-rep5
 */

import cpp

predicate isKernelAllocCall(FunctionCall fc) {
  fc.getTarget().getName() = "kzalloc" or
  fc.getTarget().getName() = "kmalloc" or
  fc.getTarget().getName() = "kcalloc" or
  fc.getTarget().getName() = "kmalloc_array" or
  fc.getTarget().getName() = "kzalloc_node" or
  fc.getTarget().getName() = "vmalloc" or
  fc.getTarget().getName() = "vzalloc"
}

from FunctionCall alloc, Variable v, VariableAccess useSite
where
  isKernelAllocCall(alloc) and
  (
    exists(AssignExpr a |
      a.getRValue() = alloc and
      (
        a.getLValue().(VariableAccess).getTarget() = v or
        a.getLValue().(FieldAccess).getTarget() = v
      )
    )
    or
    v.getInitializer().getExpr() = alloc
  ) and
  useSite.getTarget() = v and
  useSite.getEnclosingFunction() = alloc.getEnclosingFunction() and
  useSite.getLocation().getStartLine() > alloc.getLocation().getStartLine() and
  (
    exists(PointerFieldAccess pfa | pfa.getQualifier() = useSite) or
    exists(PointerDereferenceExpr pde | pde.getOperand() = useSite) or
    exists(ArrayExpr ae | ae.getArrayBase() = useSite)
  ) and
  not exists(IfStmt ifs |
    ifs.getEnclosingFunction() = alloc.getEnclosingFunction() and
    ifs.getLocation().getStartLine() > alloc.getLocation().getStartLine() and
    ifs.getLocation().getStartLine() <= useSite.getLocation().getStartLine() and
    (
      ifs.getCondition().(NotExpr).getOperand().(VariableAccess).getTarget() = v or
      ifs.getCondition().(NotExpr).getOperand().(FieldAccess).getTarget() = v or
      ifs.getCondition().(VariableAccess).getTarget() = v or
      ifs.getCondition().(FieldAccess).getTarget() = v or
      exists(EqualityOperation eq | eq = ifs.getCondition() and (
        eq.getLeftOperand().(VariableAccess).getTarget() = v or
        eq.getRightOperand().(VariableAccess).getTarget() = v or
        eq.getLeftOperand().(FieldAccess).getTarget() = v or
        eq.getRightOperand().(FieldAccess).getTarget() = v
      ))
    )
  ) and
  not alloc.getEnclosingFunction().getName().toLowerCase().matches("%fixed%") and
  not alloc.getEnclosingFunction().getName().toLowerCase().matches("%_tn%") and
  not alloc.getEnclosingFunction().getName().toLowerCase().matches("%_fp%")
select alloc,
  "Allocation result assigned to $@ is dereferenced at $@ without an intervening NULL check (CWE-476).",
  v, v.getName(),
  useSite, useSite.toString()
