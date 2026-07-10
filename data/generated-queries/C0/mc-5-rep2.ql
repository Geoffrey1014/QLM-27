/**
 * @name Missing NULL check on allocation result before dereference
 * @description Detects allocations from kmalloc-family / devm_* / dma allocator
 *              functions whose return value is later dereferenced without first
 *              being checked for NULL. Modeled after the baytrail pinctrl fix
 *              (devm_kcalloc result used without NULL check), this query
 *              generalizes to the whole family of allocators.
 * @kind problem
 * @problem.severity warning
 * @id cpp/missing-null-check-on-alloc
 * @tags reliability
 *       security
 */

import cpp
import semmle.code.cpp.controlflow.Guards
import semmle.code.cpp.dataflow.DataFlow

/**
 * Functions that return a freshly-allocated pointer which may be NULL on failure.
 * Covers the kmalloc family, devm_* variants, vmalloc family, dma allocators,
 * and a few common siblings.
 */
predicate isAllocFunction(Function f) {
  exists(string n | n = f.getName() |
    n = "kmalloc" or
    n = "kzalloc" or
    n = "kcalloc" or
    n = "kmalloc_array" or
    n = "krealloc" or
    n = "kmemdup" or
    n = "kstrdup" or
    n = "kstrndup" or
    n = "vmalloc" or
    n = "vzalloc" or
    n = "vcalloc" or
    n = "vmalloc_array" or
    n = "kvmalloc" or
    n = "kvzalloc" or
    n = "kvcalloc" or
    n = "kvmalloc_array" or
    n = "devm_kmalloc" or
    n = "devm_kzalloc" or
    n = "devm_kcalloc" or
    n = "devm_kmalloc_array" or
    n = "devm_krealloc" or
    n = "devm_kmemdup" or
    n = "devm_kstrdup" or
    n = "devm_kasprintf" or
    n = "kasprintf" or
    n = "kvasprintf" or
    n = "dma_alloc_coherent" or
    n = "dmam_alloc_coherent" or
    n = "dma_alloc_attrs" or
    n = "dma_pool_alloc" or
    n = "dma_pool_zalloc"
  )
}

/** A call to an allocator. */
class AllocCall extends FunctionCall {
  AllocCall() { isAllocFunction(this.getTarget()) }
}

/**
 * Holds if `e` is a NULL-check on `v` (directly or indirectly through a guard
 * condition that controls the basic block we reach later).
 */
predicate isNullCheckOf(Expr check, Variable v) {
  // Direct comparisons: v == NULL / v != NULL / !v / v
  exists(Expr inner |
    (
      inner = check or
      inner = check.(NotExpr).getOperand()
    ) and
    (
      // if (!v) / if (v)
      inner.(VariableAccess).getTarget() = v
      or
      // v == 0 / v == NULL / v != NULL
      exists(EqualityOperation eq |
        eq = inner and
        eq.getAnOperand().(VariableAccess).getTarget() = v and
        eq.getAnOperand().getValue() = "0"
      )
    )
  )
  or
  // IS_ERR / IS_ERR_OR_NULL style wrappers
  exists(FunctionCall fc | fc = check |
    (
      fc.getTarget().getName() = "IS_ERR" or
      fc.getTarget().getName() = "IS_ERR_OR_NULL" or
      fc.getTarget().getName() = "PTR_ERR_OR_ZERO" or
      fc.getTarget().getName() = "unlikely" or
      fc.getTarget().getName() = "likely"
    ) and
    fc.getAnArgument().(VariableAccess).getTarget() = v
  )
}

/**
 * Holds if the function `f` contains some NULL-check expression on variable `v`
 * anywhere. This is a conservative whole-function check that mirrors the
 * "did the developer ever check it?" heuristic used by Smatch/Coccinelle.
 */
predicate functionChecksVarForNull(Function f, Variable v) {
  exists(Expr e |
    e.getEnclosingFunction() = f and
    isNullCheckOf(e, v)
  )
}

/**
 * A dereference of variable `v`: either `v->field`, `*v`, `v[i]`,
 * or passing `v` to a function that the called code dereferences (here we
 * conservatively flag the obvious local dereferences only).
 */
predicate isDereferenceOf(Expr e, Variable v) {
  // p->field
  exists(PointerFieldAccess pfa |
    pfa = e and
    pfa.getQualifier().(VariableAccess).getTarget() = v
  )
  or
  // *p
  exists(PointerDereferenceExpr pde |
    pde = e and
    pde.getOperand().(VariableAccess).getTarget() = v
  )
  or
  // p[i]
  exists(ArrayExpr ae |
    ae = e and
    ae.getArrayBase().(VariableAccess).getTarget() = v
  )
}

from AllocCall alloc, Variable v, Expr deref, Function f
where
  // The allocation's result is stored into v (either via assignment or initializer).
  (
    exists(AssignExpr a |
      a.getRValue() = alloc and
      a.getLValue().(VariableAccess).getTarget() = v
    )
    or
    exists(Initializer init |
      init.getExpr() = alloc and
      init.getDeclaration() = v
    )
    or
    // p->field = alloc(...) where v is a field-like variable; capture struct-field
    // assignments where the lvalue chain ends in a field of the same name we then
    // dereference. We approximate via FieldAccess on the assignment target.
    exists(AssignExpr a, FieldAccess fa |
      a.getRValue() = alloc and
      fa = a.getLValue() and
      v = fa.getTarget()
    )
  ) and
  // There is a dereference of v in the same function as the allocation.
  f = alloc.getEnclosingFunction() and
  deref.getEnclosingFunction() = f and
  isDereferenceOf(deref, v) and
  // The function never checks v for NULL anywhere (conservative).
  not functionChecksVarForNull(f, v) and
  // Order: the dereference is reachable after the allocation textually.
  alloc.getLocation().getStartLine() < deref.getLocation().getStartLine()
select alloc,
  "Result of allocator '" + alloc.getTarget().getName() +
    "' is stored in '" + v.getName() +
    "' and later dereferenced at $@ without a NULL check.",
  deref, "this dereference"
