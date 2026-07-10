/**
 * @name Missing NULL check after kzalloc/kmalloc family allocation
 * @description Memory allocated by k*alloc/kzalloc/kmalloc family functions may
 *              fail and return NULL. Dereferencing the returned pointer (or
 *              passing it to a function that dereferences it) without first
 *              checking for NULL is a bug that can cause a NULL-pointer
 *              dereference oops in the kernel.
 * @kind problem
 * @problem.severity warning
 * @id cpp/missing-null-check-kalloc
 * @tags reliability
 *       correctness
 *       security
 */

import cpp
import semmle.code.cpp.controlflow.Guards
import semmle.code.cpp.controlflow.Dominance
import semmle.code.cpp.dataflow.DataFlow

/**
 * Kernel allocation functions in the k*alloc family whose return value may be
 * NULL on failure and therefore must be checked before use.
 */
predicate isKernelAllocFunction(Function f) {
  f.getName() =
    [
      "kmalloc", "kzalloc", "kcalloc", "kmalloc_array", "kmalloc_node",
      "kzalloc_node", "kcalloc_node", "kmalloc_array_node", "krealloc",
      "kvmalloc", "kvzalloc", "kvcalloc", "kvmalloc_node", "kvzalloc_node",
      "vmalloc", "vzalloc", "vmalloc_node", "vzalloc_node",
      "devm_kmalloc", "devm_kzalloc", "devm_kcalloc", "devm_kmalloc_array",
      "kmem_cache_alloc", "kmem_cache_zalloc", "kmem_cache_alloc_node",
      "mempool_alloc"
    ]
}

/**
 * `e` is a call to a kernel allocator.
 */
class KAllocCall extends FunctionCall {
  KAllocCall() { isKernelAllocFunction(this.getTarget()) }
}

/**
 * Holds if `v` is assigned the result of the kernel allocation `alloc`.
 * `v` may be a local variable or a field accessed through a pointer
 * (e.g. `priv->pFirmware = kzalloc(...)`).
 */
predicate allocAssignedTo(KAllocCall alloc, Expr lhs) {
  exists(AssignExpr a |
    a.getRValue() = alloc and
    lhs = a.getLValue()
  )
  or
  exists(Variable v, Initializer init |
    init.getExpr() = alloc and
    v.getInitializer() = init and
    lhs = v.getAnAccess()
  )
}

/**
 * Holds if `use` is an access to the same storage that received the
 * allocation result, in the same function as `alloc`, and on a control-flow
 * path reachable after `alloc`.
 */
predicate sameStorageUse(Expr lhs, Expr use) {
  // local variable: same Variable
  exists(Variable v |
    lhs = v.getAnAccess() and use = v.getAnAccess() and use != lhs
  )
  or
  exists(Variable v |
    lhs.(VariableAccess).getTarget() = v and
    use.(VariableAccess).getTarget() = v and
    use != lhs
  )
  or
  // field access: same Field through pointer/struct
  exists(Field f |
    lhs.(FieldAccess).getTarget() = f and
    use.(FieldAccess).getTarget() = f and
    use != lhs
  )
}

/**
 * `use` is a "dangerous" use of the allocated pointer that would dereference
 * it: a pointer dereference, field access (->), array index, or being passed
 * to a function that would expect a valid pointer (memcpy/memset/strcpy and
 * other string/mem ops).
 */
predicate dangerousUse(Expr use) {
  // explicit dereference *p
  exists(PointerDereferenceExpr d | d.getOperand() = use)
  or
  // p->field
  exists(FieldAccess fa | fa.getQualifier() = use and fa.getTarget().getDeclaringType() instanceof Struct)
  or
  // p[i]
  exists(ArrayExpr ae | ae.getArrayBase() = use)
  or
  // passed to a memory-init/copy function that will dereference
  exists(FunctionCall fc, int i |
    fc.getArgument(i) = use and
    fc.getTarget().getName() =
      ["memcpy", "memset", "memmove", "strcpy", "strncpy", "strcat",
       "strlcpy", "strscpy", "memcpy_s", "__memcpy", "__memset",
       "copy_from_user", "copy_to_user"]
  )
}

/**
 * Holds if there is a NULL-check on the same storage in the same function,
 * dominating `use`.
 */
predicate hasNullCheckBefore(Expr lhs, Expr use) {
  // simple `if (!p)` / `if (p == NULL)` style: any condition mentioning the same storage
  exists(IfStmt ifs, Expr cond, Expr checked |
    cond = ifs.getCondition() and
    checked = cond.getAChild*() and
    sameStorageUse(lhs, checked) and
    ifs.getLocation().getStartLine() < use.getLocation().getStartLine() and
    ifs.getEnclosingFunction() = use.getEnclosingFunction()
  )
  or
  // checked inside a logical expression (e.g. `if (!a || !b)`)
  exists(LogicalAndExpr la, Expr checked |
    checked = la.getAChild*() and
    sameStorageUse(lhs, checked) and
    la.getLocation().getStartLine() < use.getLocation().getStartLine() and
    la.getEnclosingFunction() = use.getEnclosingFunction()
  )
  or
  // ternary `p ? ... : ...`
  exists(ConditionalExpr ce, Expr checked |
    checked = ce.getCondition().getAChild*() and
    sameStorageUse(lhs, checked) and
    ce.getLocation().getStartLine() < use.getLocation().getStartLine() and
    ce.getEnclosingFunction() = use.getEnclosingFunction()
  )
}

from KAllocCall alloc, Expr lhs, Expr use
where
  allocAssignedTo(alloc, lhs) and
  sameStorageUse(lhs, use) and
  dangerousUse(use) and
  alloc.getEnclosingFunction() = use.getEnclosingFunction() and
  // use is reachable after alloc in CFG
  alloc.getASuccessor+() = use and
  // no NULL check guards this use
  not hasNullCheckBefore(lhs, use) and
  // exclude obvious cases where the assignment site itself is what we're looking at
  use.getLocation().getStartLine() > alloc.getLocation().getStartLine()
select use,
  "Pointer assigned from $@ is used here without a prior NULL check; allocation may fail.",
  alloc, alloc.getTarget().getName()
