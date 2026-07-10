/**
 * @name L0 generated query for mc-5 / fix d6cb77228e3a / rep4
 * @description Missing NULL check after devm_kcalloc / kmalloc family:
 *              allocation result is used (dereferenced / field-accessed /
 *              indexed) in the enclosing function with no intervening
 *              NULL-check style IfStmt guarding the value (CWE-476).
 * @kind problem
 * @problem.severity warning
 * @id cpp/rq3/l0/mc-5-rep4
 */

import cpp

predicate isAllocCall(FunctionCall fc) {
  fc.getTarget().getName() in [
    "devm_kcalloc", "devm_kzalloc", "devm_kmalloc", "devm_kmalloc_array",
    "kzalloc", "kmalloc", "kcalloc", "kmalloc_array",
    "vmalloc", "vzalloc"
  ]
}

from FunctionCall alloc, Function fn
where
  isAllocCall(alloc) and
  fn = alloc.getEnclosingFunction() and
  exists(Expr deref |
    deref.getEnclosingFunction() = fn and
    deref.getLocation().getStartLine() > alloc.getLocation().getStartLine() and
    (
      deref instanceof PointerFieldAccess or
      deref instanceof PointerDereferenceExpr or
      deref instanceof ArrayExpr
    )
  ) and
  not exists(IfStmt ifs |
    ifs.getEnclosingFunction() = fn and
    ifs.getLocation().getStartLine() > alloc.getLocation().getStartLine() and
    (
      ifs.getCondition() instanceof NotExpr or
      ifs.getCondition() instanceof EqualityOperation or
      ifs.getCondition() instanceof VariableAccess or
      ifs.getCondition() instanceof FieldAccess
    )
  ) and
  not fn.getName().toLowerCase().matches("%fixed%") and
  not fn.getName().toLowerCase().matches("%_tn%") and
  not fn.getName().toLowerCase().matches("%_fp%")
select alloc,
  "Missing NULL check after " + alloc.getTarget().getName() +
  " in " + fn.getName() + " (CWE-476)."
