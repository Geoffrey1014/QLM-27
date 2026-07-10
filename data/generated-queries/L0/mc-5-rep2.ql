/**
 * @name Missing NULL check after devm_* allocator
 * @description Detects a call to devm_kcalloc / devm_kzalloc / devm_kmalloc
 *              whose result is stored into a variable that is subsequently
 *              dereferenced (via field access, pointer deref, or array
 *              subscript) in the same function without any intervening
 *              NULL check on that variable. Pattern derived from upstream
 *              commit d6cb77228e3a ("pinctrl: baytrail: Fix potential NULL
 *              pointer dereference").
 * @kind problem
 * @problem.severity error
 * @id qlm/l0-mc5-missing-null-check-devm-alloc
 * @tags reliability
 *       missing-check
 *       external/cwe/cwe-476
 */

import cpp

predicate isDevmAllocApi(FunctionCall fc) {
  fc.getTarget().getName() = "devm_kcalloc" or
  fc.getTarget().getName() = "devm_kzalloc" or
  fc.getTarget().getName() = "devm_kmalloc"
}

/* A NULL-check on `v` inside function `f` at line `line`.
 * We look for either
 *   if (!v) ...     — LogicalNotExpr wrapping an access of v
 *   if (v == 0) ... — EQExpr with one operand being an access of v
 *                      and the other a zero literal
 *   if (v != 0) ... — NEExpr with the same shape
 *   if (v) ...      — plain expression access of v used as boolean
 */
predicate nullCheckOn(Function f, int line, Variable v) {
  exists(IfStmt ifs, Expr cond |
    ifs.getEnclosingFunction() = f and
    ifs.getLocation().getStartLine() = line and
    cond = ifs.getCondition() and
    (
      cond.(NotExpr).getOperand().(VariableAccess).getTarget() = v
      or
      cond.(VariableAccess).getTarget() = v
      or
      exists(EQExpr eq |
        eq = cond and
        eq.getAnOperand().(VariableAccess).getTarget() = v and
        eq.getAnOperand().getValue() = "0"
      )
      or
      exists(NEExpr ne |
        ne = cond and
        ne.getAnOperand().(VariableAccess).getTarget() = v and
        ne.getAnOperand().getValue() = "0"
      )
    )
  )
}

/* A dereference of `v` inside function `f` at line `line`. */
predicate derefOf(Function f, int line, Variable v) {
  exists(VariableAccess va |
    va.getTarget() = v and
    va.getEnclosingFunction() = f and
    va.getLocation().getStartLine() = line and
    (
      exists(PointerFieldAccess pfa | pfa.getQualifier() = va)
      or
      exists(PointerDereferenceExpr pde | pde.getOperand() = va)
      or
      exists(ArrayExpr ae | ae.getArrayBase() = va)
    )
  )
}

from FunctionCall alloc, Assignment assign, Variable v, VariableAccess useAccess, int allocLine, int useLine
where
  isDevmAllocApi(alloc) and
  assign.getRValue() = alloc and
  assign.getLValue().(VariableAccess).getTarget() = v and
  allocLine = alloc.getLocation().getStartLine() and
  useAccess.getTarget() = v and
  useAccess.getEnclosingFunction() = alloc.getEnclosingFunction() and
  useLine = useAccess.getLocation().getStartLine() and
  useLine > allocLine and
  derefOf(alloc.getEnclosingFunction(), useLine, v) and
  not exists(int checkLine |
    nullCheckOn(alloc.getEnclosingFunction(), checkLine, v) and
    checkLine > allocLine and
    checkLine <= useLine
  )
select alloc,
  "Missing NULL check: result of " + alloc.getTarget().getName() +
  " assigned to '" + v.getName() +
  "' is dereferenced at line " + useLine +
  " without an intervening NULL check in " +
  alloc.getEnclosingFunction().getName() + "."
