/**
 * @name Missing NULL check after kzalloc/kmalloc family allocation
 * @description An allocation via kzalloc/kmalloc/kcalloc/kmalloc_array (and friends) may
 *              fail and return NULL. If the result is stored into a variable (including
 *              a struct field) and subsequently dereferenced without a NULL check on any
 *              path from the allocation to the use, the kernel may oops on allocation
 *              failure. This generalizes the rtl8192u priv->pFirmware fix to all kernel
 *              allocators in the k*alloc family.
 * @kind problem
 * @problem.severity error
 * @id cpp/missing-null-check-kalloc
 * @tags reliability
 *       correctness
 *       security
 */

import cpp
import semmle.code.cpp.controlflow.Guards
import semmle.code.cpp.controlflow.SSA

/** A call to a kernel allocator that may return NULL on failure. */
class KernelAllocCall extends FunctionCall {
  KernelAllocCall() {
    this.getTarget().getName() =
      [
        "kmalloc", "kzalloc", "kcalloc", "kmalloc_array", "kzalloc_node",
        "kmalloc_node", "kmalloc_array_node", "kcalloc_node",
        "kmemdup", "kmemdup_nul", "kstrdup", "kstrndup",
        "vmalloc", "vzalloc", "vmalloc_node", "vzalloc_node",
        "kvmalloc", "kvzalloc", "kvmalloc_node", "kvzalloc_node",
        "devm_kmalloc", "devm_kzalloc", "devm_kcalloc", "devm_kmalloc_array",
        "krealloc", "kvrealloc"
      ]
  }
}

/**
 * An expression that effectively tests whether `e` is NULL (directly or via the
 * variable/field it was stored into).
 */
predicate isNullCheckOf(Expr guard, Expr value) {
  // Direct guard on the same expression's value via guard analysis.
  exists(GuardCondition gc | gc = guard |
    gc.(Expr).getAChild*() = value
    or
    exists(Variable v |
      value = v.getAnAccess() and
      gc.(Expr).getAChild*() = v.getAnAccess()
    )
    or
    exists(Field f, FieldAccess fa1, FieldAccess fa2 |
      fa1 = value and fa1.getTarget() = f and
      fa2.getTarget() = f and gc.(Expr).getAChild*() = fa2
    )
  )
}

/** Holds if `use` is a dereference (`->`, `*`, or array index) of expression `base`. */
predicate isDereferenceOf(Expr use, Expr base) {
  exists(PointerFieldAccess pfa | pfa = use and pfa.getQualifier() = base)
  or
  exists(PointerDereferenceExpr pde | pde = use and pde.getOperand() = base)
  or
  exists(ArrayExpr ae | ae = use and ae.getArrayBase() = base)
}

/**
 * Holds if `alloc` is assigned (directly) to lvalue `target` in a single
 * assignment expression.
 */
predicate allocAssignedTo(KernelAllocCall alloc, Expr target) {
  exists(AssignExpr ae | ae.getRValue() = alloc and ae.getLValue() = target)
  or
  exists(Initializer init, Variable v |
    init.getExpr() = alloc and init.getDeclaration() = v and
    target = v.getAnAccess()
  )
}

/**
 * Holds if `subsequent` is a use of the same storage written by `target` that
 * follows the allocation in the same function, and there is no NULL guard on
 * the value between them.
 */
predicate dereferencedWithoutCheck(KernelAllocCall alloc, Expr subsequent) {
  exists(Expr target, Function f |
    allocAssignedTo(alloc, target) and
    alloc.getEnclosingFunction() = f and
    subsequent.getEnclosingFunction() = f and
    // target is either a variable access or a field access; match the use accordingly
    (
      // Variable case
      exists(Variable v |
        target = v.getAnAccess() and
        isDereferenceOf(subsequent, v.getAnAccess())
      )
      or
      // Field-access case (e.g. priv->pFirmware): match by field
      exists(Field fld, FieldAccess writeFa, FieldAccess readFa |
        target = writeFa and writeFa.getTarget() = fld and
        readFa.getTarget() = fld and
        isDereferenceOf(subsequent, readFa)
      )
    ) and
    // The use must syntactically come after the allocation in the function.
    alloc.getLocation().getStartLine() < subsequent.getLocation().getStartLine() and
    // No NULL check on the allocated value between alloc and the use.
    not exists(Expr guard |
      isNullCheckOf(guard, target) and
      guard.getEnclosingFunction() = f and
      guard.getLocation().getStartLine() >= alloc.getLocation().getStartLine() and
      guard.getLocation().getStartLine() <= subsequent.getLocation().getStartLine()
    )
  )
}

from KernelAllocCall alloc, Expr use
where
  dereferencedWithoutCheck(alloc, use) and
  // Reduce noise: skip allocations inside macro expansions.
  not alloc.isInMacroExpansion()
select alloc,
  "Allocation from $@ may return NULL but the result is dereferenced at $@ without a NULL check.",
  alloc.getTarget(), alloc.getTarget().getName(), use, use.toString()
