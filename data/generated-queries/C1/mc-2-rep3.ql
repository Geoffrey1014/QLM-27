/**
 * @name Missing NULL check on allocation result before dereference
 * @description Detects assignments of an allocation function result
 *              (kzalloc / kmalloc / kcalloc / vmalloc / kmemdup / etc.)
 *              to a variable or field where the allocated pointer is
 *              subsequently dereferenced without any intervening NULL
 *              check on the same access path. This is the C1 monolithic
 *              detector for the missing-check (mc) pattern; the POC
 *              oracle is a kzalloc into priv->pFirmware followed by
 *              priv->pFirmware->firmware_status with no `if (!...)`.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-mc-2
 */

import cpp

/* Allocation APIs whose return value can be NULL on failure. */
predicate isAllocApi(string name) {
  name = "kzalloc" or
  name = "kmalloc" or
  name = "kcalloc" or
  name = "kmalloc_array" or
  name = "kvmalloc" or
  name = "kvzalloc" or
  name = "vmalloc" or
  name = "vzalloc" or
  name = "kmemdup" or
  name = "kstrdup" or
  name = "kasprintf" or
  name = "devm_kzalloc" or
  name = "devm_kmalloc" or
  name = "malloc" or
  name = "calloc" or
  name = "realloc"
}

/* The allocation call. */
class AllocCall extends FunctionCall {
  AllocCall() { isAllocApi(this.getTarget().getName()) }
}

/* A check that proves the expression is non-NULL. We treat the
 * following as evidence of a NULL check on `e` (textual access-path
 * match is conservative but sufficient for the POC oracle):
 *   if (!e) ...     /  if (e == NULL) ...
 *   if (e)  ...     /  if (e != NULL) ...
 *   BUG_ON(!e), WARN_ON(!e)
 */
predicate isNullCheckOn(Expr cond, string accessText) {
  exists(Expr inner |
    (
      inner = cond or
      inner = cond.(NotExpr).getOperand() or
      inner = cond.(EQExpr).getAnOperand() or
      inner = cond.(NEExpr).getAnOperand()
    ) and
    inner.toString() = accessText
  )
}

/* A dereference / field access through the allocation target. We
 * recognise both pointer-arrow uses (`p->f`) and explicit dereferences
 * (`*p`). The access path of the base expression is captured as text
 * so it can be matched against earlier checks and earlier writes.
 */
predicate isDerefOf(Expr e, string accessText) {
  exists(PointerFieldAccess pfa |
    e = pfa and pfa.getQualifier().toString() = accessText
  )
  or
  exists(PointerDereferenceExpr pde |
    e = pde and pde.getOperand().toString() = accessText
  )
  or
  exists(ArrayExpr ae |
    e = ae and ae.getArrayBase().toString() = accessText
  )
}

from AllocCall alloc, Assignment store, Expr lhs, Expr deref,
     Function fn, string accessText
where
  /* alloc result is stored into `lhs` (a Variable or FieldAccess). */
  store.getRValue() = alloc and
  lhs = store.getLValue() and
  accessText = lhs.toString() and
  /* `deref` dereferences the same access path, later in the same fn. */
  fn = alloc.getEnclosingFunction() and
  fn = deref.getEnclosingFunction() and
  isDerefOf(deref, accessText) and
  deref.getLocation().getStartLine() > alloc.getLocation().getStartLine() and
  /* No intervening NULL check on the same access path, in same fn. */
  not exists(IfStmt ifs, Expr cond |
    ifs.getEnclosingFunction() = fn and
    cond = ifs.getCondition() and
    isNullCheckOn(cond, accessText) and
    ifs.getLocation().getStartLine() > alloc.getLocation().getStartLine() and
    ifs.getLocation().getStartLine() <= deref.getLocation().getStartLine()
  ) and
  /* And no re-assignment between the alloc and the deref (would mask). */
  not exists(Assignment a2 |
    a2.getEnclosingFunction() = fn and
    a2.getLValue().toString() = accessText and
    a2.getLocation().getStartLine() > alloc.getLocation().getStartLine() and
    a2.getLocation().getStartLine() < deref.getLocation().getStartLine() and
    a2 != store
  )
select alloc,
  "Allocation result stored in '" + accessText +
  "' is dereferenced at $@ without a preceding NULL check.",
  deref, deref.toString()
