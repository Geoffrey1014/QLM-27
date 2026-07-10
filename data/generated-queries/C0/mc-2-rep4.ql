/**
 * @name Missing NULL check after allocation function
 * @description Detects calls to memory allocation functions (kzalloc, kmalloc, kcalloc,
 *              vmalloc, etc.) whose result is assigned to a variable that is subsequently
 *              dereferenced or passed onward without any NULL check on a reachable path.
 *              Allocation can fail (returning NULL), so an unchecked dereference can
 *              cause a NULL-pointer dereference at runtime.
 * @kind problem
 * @problem.severity error
 * @id cpp/missing-null-check-after-alloc
 * @tags reliability
 *       security
 */

import cpp
import semmle.code.cpp.controlflow.Guards
import semmle.code.cpp.dataflow.DataFlow

/** Holds if `f` is a kernel allocation function that may return NULL. */
predicate isAllocFunction(Function f) {
  f.getName() = "kzalloc" or
  f.getName() = "kmalloc" or
  f.getName() = "kcalloc" or
  f.getName() = "kmalloc_array" or
  f.getName() = "kmemdup" or
  f.getName() = "kstrdup" or
  f.getName() = "kstrndup" or
  f.getName() = "vmalloc" or
  f.getName() = "vzalloc" or
  f.getName() = "vmalloc_node" or
  f.getName() = "kvmalloc" or
  f.getName() = "kvzalloc" or
  f.getName() = "devm_kzalloc" or
  f.getName() = "devm_kmalloc" or
  f.getName() = "devm_kcalloc"
}

/** An allocation call expression. */
class AllocCall extends FunctionCall {
  AllocCall() { isAllocFunction(this.getTarget()) }
}

/**
 * Holds if `e` is a check that compares `v` against NULL (directly or via `!v`).
 */
predicate isNullCheck(Expr e, Expr v) {
  // if (!ptr) or if (ptr)
  exists(NotExpr n | n = e and n.getOperand() = v)
  or
  // if (ptr == NULL) or (ptr != NULL) or (NULL == ptr) ...
  exists(EqualityOperation eq |
    eq = e and
    (
      eq.getAnOperand() = v and eq.getAnOperand().getValue() = "0"
      or
      eq.getAnOperand() = v and eq.getAnOperand() instanceof NullValue
    )
  )
  or
  // bare use in a boolean position: if (ptr) { ... }
  e = v
}

/**
 * Holds if some control-flow node guards `use` such that on the path to `use`,
 * the variable `v` (which received the alloc result) has been NULL-checked.
 */
predicate guardedByNullCheck(Variable v, Expr use) {
  exists(GuardCondition g, VariableAccess va |
    va.getTarget() = v and
    va.getParent*() = g and
    (g.controls(use.getBasicBlock(), true) or g.controls(use.getBasicBlock(), false))
  )
}

/**
 * Holds if `use` is a dereference-like use of `v`: field access, array index,
 * pointer dereference, or passed to a function that will dereference it.
 */
predicate isDereferenceUse(Variable v, Expr use) {
  exists(VariableAccess va | va = use and va.getTarget() = v |
    // p->field or (*p).field
    exists(FieldAccess fa | fa.getQualifier() = va)
    or
    // *p
    exists(PointerDereferenceExpr d | d.getOperand() = va)
    or
    // p[i]
    exists(ArrayExpr ae | ae.getArrayBase() = va)
  )
}

from AllocCall alloc, Variable v, VariableAccess derefAccess
where
  // The allocation result is assigned to v.
  exists(AssignExpr a |
    a.getRValue() = alloc and
    a.getLValue().(VariableAccess).getTarget() = v
  )
  or
  exists(Initializer init |
    init.getExpr() = alloc and
    init.getDeclaration() = v
  )
  // The variable v is later dereferenced in the same function.
  and isDereferenceUse(v, derefAccess)
  and derefAccess.getEnclosingFunction() = alloc.getEnclosingFunction()
  // The dereference is not guarded by a null check on v.
  and not guardedByNullCheck(v, derefAccess)
  // Avoid matching the same statement as the allocation itself.
  and derefAccess.getLocation().getStartLine() > alloc.getLocation().getStartLine()
select alloc,
  "Result of allocation '" + alloc.getTarget().getName() +
    "' is later dereferenced via $@ without a NULL check.",
  derefAccess, derefAccess.toString()
