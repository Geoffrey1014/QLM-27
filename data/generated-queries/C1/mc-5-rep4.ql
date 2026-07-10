/**
 * @name Missing NULL check after allocator return
 * @description The return value of a memory allocator (e.g. devm_kcalloc,
 *              kmalloc, kzalloc, kcalloc, devm_kmalloc, devm_kzalloc) is
 *              stored into a variable or field and then used (dereferenced
 *              or passed onward) without first being compared to NULL.
 *              A NULL return from the allocator therefore leads to a
 *              potential NULL pointer dereference.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-mc-5
 */

import cpp

/* Names of allocator functions whose return value may be NULL on failure. */
predicate isAllocator(string name) {
  name = "kmalloc" or
  name = "kzalloc" or
  name = "kcalloc" or
  name = "krealloc" or
  name = "kmalloc_array" or
  name = "kvmalloc" or
  name = "kvzalloc" or
  name = "kvcalloc" or
  name = "vmalloc" or
  name = "vzalloc" or
  name = "devm_kmalloc" or
  name = "devm_kzalloc" or
  name = "devm_kcalloc" or
  name = "devm_kmalloc_array" or
  name = "malloc" or
  name = "calloc" or
  name = "realloc"
}

class AllocCall extends FunctionCall {
  AllocCall() { isAllocator(this.getTarget().getName()) }
}

/* An expression that references the same storage location as `lv`.
   We support two cases:
     - lv is a local variable access:        match other VariableAccess to
       the same Variable.
     - lv is a field-of-pointer access:      match other PointerFieldAccess
       to the same Field where the qualifier resolves to the same base
       variable.
*/
predicate sameStorage(Expr lv, Expr other) {
  exists(Variable v |
    lv = v.getAnAccess() and
    other = v.getAnAccess()
  )
  or
  exists(PointerFieldAccess a, PointerFieldAccess b, Variable base |
    a = lv and b = other and
    a.getTarget() = b.getTarget() and
    a.getQualifier().(VariableAccess).getTarget() = base and
    b.getQualifier().(VariableAccess).getTarget() = base
  )
  or
  exists(FieldAccess a, FieldAccess b |
    a = lv and b = other and
    a.getTarget() = b.getTarget() and
    a.getQualifier().toString() = b.getQualifier().toString()
  )
}

/* Is `e` a NULL-check that tests the same storage as `lv`? */
predicate isNullCheckOf(Expr e, Expr lv) {
  // !X
  exists(NotExpr ne | ne = e and sameStorage(lv, ne.getOperand()))
  or
  // X == 0 / 0 == X / X != 0 / 0 != X (NULL literal compares as int 0)
  exists(EqualityOperation eq, Expr a, Expr b |
    eq = e and a = eq.getLeftOperand() and b = eq.getRightOperand() and
    (
      (sameStorage(lv, a) and b.getValue().toInt() = 0)
      or
      (sameStorage(lv, b) and a.getValue().toInt() = 0)
    )
  )
  or
  // if (X)  -- direct boolean context
  exists(IfStmt ifs | e = ifs.getCondition() and sameStorage(lv, e))
  or
  // IS_ERR / IS_ERR_OR_NULL / PTR_ERR_OR_ZERO style
  exists(FunctionCall fc |
    fc = e and
    (fc.getTarget().getName() = "IS_ERR" or
     fc.getTarget().getName() = "IS_ERR_OR_NULL" or
     fc.getTarget().getName() = "PTR_ERR_OR_ZERO") and
    sameStorage(lv, fc.getAnArgument())
  )
}

/* A "dangerous use" of `use` (read access to the assigned storage) that
   would crash if the pointer is NULL or that propagates it onward. */
predicate isDangerousUse(Expr use) {
  exists(PointerFieldAccess pfa | pfa.getQualifier() = use)
  or
  exists(PointerDereferenceExpr d | d.getOperand() = use)
  or
  exists(ArrayExpr a | a.getArrayBase() = use)
  or
  exists(FunctionCall fc |
    fc.getAnArgument() = use and
    not isAllocator(fc.getTarget().getName()) and
    not fc.getTarget().getName().regexpMatch("(?i).*(free|put|release|destroy).*")
  )
}

from AllocCall alloc, Expr assignedTo, Expr use, Function f
where
  f = alloc.getEnclosingFunction() and
  // The allocator's return value is stored to a variable or field.
  (
    exists(AssignExpr ae |
      ae.getRValue() = alloc and assignedTo = ae.getLValue()
    )
    or
    exists(LocalVariable v |
      v.getInitializer().getExpr() = alloc and
      assignedTo = v.getAnAccess()
    )
  ) and
  assignedTo.getEnclosingFunction() = f and
  // A later read of the same storage is dangerously used.
  use.getEnclosingFunction() = f and
  sameStorage(assignedTo, use) and
  use != assignedTo and
  isDangerousUse(use) and
  // The use is reachable after the allocation.
  alloc.getASuccessor+() = use and
  // No NULL check on the same storage occurs between alloc and use.
  not exists(Expr check |
    check.getEnclosingFunction() = f and
    isNullCheckOf(check, assignedTo) and
    alloc.getASuccessor+() = check and
    check.getASuccessor+() = use
  )
select alloc,
  "Return value of allocator '" + alloc.getTarget().getName() +
  "' is used at $@ without a prior NULL check; allocation failure leads to NULL deref.",
  use, "this site"
