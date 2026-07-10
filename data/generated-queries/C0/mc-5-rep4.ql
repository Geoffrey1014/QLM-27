/**
 * @name Missing NULL check after devm_kcalloc/devm_kzalloc/devm_kmalloc allocation
 * @description Allocations performed by the devm_k*alloc family of functions may
 *              return NULL on allocation failure. Failing to check the returned
 *              pointer before subsequent dereference may lead to a NULL pointer
 *              dereference. This query flags calls whose result is stored and then
 *              used (directly or via a field write) without a preceding NULL
 *              guard on that pointer.
 * @kind problem
 * @problem.severity error
 * @id cpp/missing-null-check-devm-alloc
 * @tags reliability
 *       correctness
 *       security
 */

import cpp
import semmle.code.cpp.controlflow.Guards
import semmle.code.cpp.controlflow.ControlFlowGraph

/**
 * Allocation functions in the kernel that can return NULL and whose result
 * must be NULL-checked before use. We deliberately focus on the devm_k*
 * family (the API in the patch) and the closely related kmalloc family
 * since they all share the "returns NULL on failure" semantics.
 */
predicate isAllocCall(FunctionCall fc) {
  exists(string n | n = fc.getTarget().getName() |
    n = "devm_kcalloc" or
    n = "devm_kzalloc" or
    n = "devm_kmalloc" or
    n = "devm_kmalloc_array" or
    n = "devm_kmemdup" or
    n = "devm_kstrdup" or
    n = "devm_krealloc"
  )
}

/**
 * The expression `e` is a NULL constant or equivalent.
 */
predicate isNullConst(Expr e) {
  e instanceof NullValue
  or
  e.getValue() = "0"
  or
  e instanceof Literal and e.getValue() = "0"
}

/**
 * The guard condition `g` tests whether `target` is NULL (or non-NULL).
 * Covers `!p`, `p == NULL`, `p != NULL`, `if (p)`.
 */
predicate guardsOnNullness(Expr g, Expr target) {
  // !p
  exists(NotExpr n | n = g and n.getOperand() = target)
  or
  // p == NULL  /  p != NULL  /  NULL == p / NULL != p
  exists(EqualityOperation eo | eo = g |
    (eo.getLeftOperand() = target and isNullConst(eo.getRightOperand())) or
    (eo.getRightOperand() = target and isNullConst(eo.getLeftOperand()))
  )
  or
  // if (p)  — implicit non-null test
  g = target
}

/**
 * There is some control-flow guard on `target` that occurs between
 * `alloc` and `use` (i.e. dominates `use` after `alloc`).
 */
predicate hasNullCheckBetween(Expr alloc, Expr target, Expr use) {
  exists(GuardCondition gc |
    guardsOnNullness(gc, target) and
    gc.(ControlFlowNode).getASuccessor*() = use and
    alloc.(ControlFlowNode).getASuccessor*() = gc
  )
}

/**
 * `e` references the same storage location as the LHS of `assign`.
 * Either a direct variable reference, or a same-field access on the same base.
 */
predicate sameLocation(Expr lhs, Expr ref) {
  // direct variable
  exists(Variable v |
    lhs = v.getAnAccess() and ref = v.getAnAccess()
  )
  or
  // field access on (likely) the same base
  exists(FieldAccess fa1, FieldAccess fa2 |
    fa1 = lhs and fa2 = ref and
    fa1.getTarget() = fa2.getTarget()
  )
}

/**
 * `use` is a subsequent dereference of `target` (either explicit `*p`,
 * pointer arith, field access via `->`, or array index).
 */
predicate isDeref(Expr use, Expr target) {
  exists(PointerFieldAccess pfa | pfa = use and sameLocation(target, pfa.getQualifier()))
  or
  exists(PointerDereferenceExpr pd | pd = use and sameLocation(target, pd.getOperand()))
  or
  exists(ArrayExpr ae | ae = use and sameLocation(target, ae.getArrayBase()))
}

from FunctionCall alloc, Expr lhs, Expr use, Function f
where
  isAllocCall(alloc) and
  // The allocation result is assigned to lhs (either a local or a struct field).
  exists(AssignExpr ae |
    ae.getRValue() = alloc and
    ae.getLValue() = lhs
  ) and
  f = alloc.getEnclosingFunction() and
  use.getEnclosingFunction() = f and
  isDeref(use, lhs) and
  alloc.(ControlFlowNode).getASuccessor+() = use and
  not hasNullCheckBetween(alloc, lhs, use)
select alloc,
  "Result of " + alloc.getTarget().getName() +
    "() may be NULL and is dereferenced at $@ without a NULL check.",
  use, "this use"
