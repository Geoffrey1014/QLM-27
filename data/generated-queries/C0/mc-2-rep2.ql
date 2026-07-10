/**
 * @name Missing NULL check after kzalloc/kmalloc allocation
 * @description An allocation via kzalloc/kmalloc/kcalloc/kvmalloc family may return NULL
 *              on failure. If the returned pointer is stored into a struct field or local
 *              variable and subsequently dereferenced without a NULL check, a NULL pointer
 *              dereference may occur. This pattern matches the rtl8192u r8192U_core.c
 *              missing-check bug, but generalizes to any kernel allocator returning NULL
 *              on failure.
 * @kind problem
 * @problem.severity warning
 * @id cpp/linux-missing-null-check-kalloc
 * @tags reliability
 *       correctness
 *       security
 */

import cpp
import semmle.code.cpp.controlflow.Guards
import semmle.code.cpp.dataflow.DataFlow

/**
 * Kernel allocator functions that return NULL on failure.
 */
class KernelAllocator extends Function {
  KernelAllocator() {
    this.getName() in [
        "kmalloc", "kzalloc", "kcalloc", "kmalloc_array",
        "kvmalloc", "kvzalloc", "kvcalloc", "kvmalloc_array",
        "vmalloc", "vzalloc", "vcalloc",
        "kmemdup", "kstrdup", "kstrndup",
        "devm_kmalloc", "devm_kzalloc", "devm_kcalloc",
        "kmem_cache_alloc", "kmem_cache_zalloc",
        "alloc_skb", "dev_alloc_skb", "netdev_alloc_skb"
      ]
  }
}

/**
 * A call to a kernel allocator.
 */
class AllocCall extends FunctionCall {
  AllocCall() { this.getTarget() instanceof KernelAllocator }
}

/**
 * Holds if `e` is some expression that references the LHS pointer (variable or field access).
 */
predicate refersToSameStorage(Expr a, Expr b) {
  // both are accesses to the same local variable
  exists(LocalScopeVariable v |
    a.(VariableAccess).getTarget() = v and
    b.(VariableAccess).getTarget() = v
  )
  or
  // both are accesses to the same field with the same qualifier variable
  exists(Field f, Variable q |
    a.(FieldAccess).getTarget() = f and
    b.(FieldAccess).getTarget() = f and
    a.(FieldAccess).getQualifier().(VariableAccess).getTarget() = q and
    b.(FieldAccess).getQualifier().(VariableAccess).getTarget() = q
  )
}

/**
 * Holds if there is a NULL-check on the same storage as `lhs` after `alloc` in the same
 * function.
 */
predicate hasNullCheckAfter(AllocCall alloc, Expr lhs) {
  exists(Expr checked, Expr cond |
    checked.getEnclosingFunction() = alloc.getEnclosingFunction() and
    refersToSameStorage(checked, lhs) and
    (
      // !checked or checked == 0 inside a condition
      cond.(NotExpr).getOperand() = checked
      or
      exists(EqualityOperation eq |
        eq = cond and eq.getAnOperand() = checked
      )
      or
      // implicit truth-test: if (checked) ...
      exists(ControlStructure cs | cs.getControllingExpr() = checked and checked = cond)
    ) and
    // ordering: the check is reachable after the alloc
    alloc.getASuccessor+() = cond
  )
}

/**
 * Holds if `use` is a dereference of the same storage as `lhs`, after the allocation.
 */
predicate hasDerefAfter(AllocCall alloc, Expr lhs) {
  exists(Expr use |
    use.getEnclosingFunction() = alloc.getEnclosingFunction() and
    refersToSameStorage(use, lhs) and
    alloc.getASuccessor+() = use and
    (
      // *use or use->field or use[i]
      exists(PointerDereferenceExpr d | d.getOperand() = use)
      or
      exists(PointerFieldAccess pfa | pfa.getQualifier() = use)
      or
      exists(ArrayExpr ae | ae.getArrayBase() = use)
    )
  )
}

from AllocCall alloc, Expr lhs
where
  // alloc's return value is assigned to lhs (variable or struct field)
  exists(AssignExpr a | a.getRValue() = alloc and a.getLValue() = lhs)
  and
  // there is a subsequent dereference of lhs
  hasDerefAfter(alloc, lhs)
  and
  // there is NO null check between alloc and the deref
  not hasNullCheckAfter(alloc, lhs)
select alloc,
  "Allocation via $@ stored into pointer is dereferenced without a NULL check on failure path.",
  alloc.getTarget(), alloc.getTarget().getName()
