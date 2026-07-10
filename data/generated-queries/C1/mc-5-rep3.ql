/**
 * @name Missing NULL check on allocator return value before dereference
 * @description An allocation routine (kmalloc / kcalloc / kzalloc /
 *              devm_kmalloc / devm_kcalloc / devm_kzalloc, etc.) returns
 *              a pointer that may be NULL on failure. The returned
 *              pointer is stored (directly into a local variable or into
 *              a struct field) and subsequently dereferenced without any
 *              intervening NULL check on that destination. This is the
 *              classic missing-NULL-check defect class.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-mc-5
 */

import cpp

/* ---------------------------------------------------------------------
 * Allocator API set. Intentionally restricted to kernel/libc allocation
 * functions that follow the "returns NULL on OOM" contract. Avoid
 * generic factory functions whose NULL semantics are mixed.
 * ------------------------------------------------------------------- */
predicate isAllocator(string name) {
  name = "kmalloc" or name = "kzalloc" or name = "kcalloc" or
  name = "krealloc" or name = "kmalloc_array" or name = "kvmalloc" or
  name = "kvzalloc" or name = "kvcalloc" or
  name = "devm_kmalloc" or name = "devm_kzalloc" or
  name = "devm_kcalloc" or name = "devm_kmalloc_array" or
  name = "vmalloc" or name = "vzalloc" or
  name = "malloc" or name = "calloc" or name = "realloc"
}

/* A NULL test on the expression `e` (covers !e, e == NULL, e == 0,
 * NULL == e, 0 == e, and the implicit boolean coercion `if (!e)` /
 * `if (e)`). We treat any guard that resolves to a NotExpr or an
 * equality-to-zero on `e` as a NULL check. */
predicate isNullCheckExpr(Expr guard, Expr target) {
  // !target
  exists(NotExpr n |
    n = guard and n.getOperand() = target
  )
  or
  // target == 0  /  0 == target  /  target == NULL
  exists(EQExpr eq, Expr z |
    eq = guard and
    (
      (eq.getLeftOperand() = target and z = eq.getRightOperand())
      or
      (eq.getRightOperand() = target and z = eq.getLeftOperand())
    ) and
    z.getValue() = "0"
  )
  or
  // implicit boolean: if (target) ... — we accept the access itself as
  // a guard when it appears directly as a condition (handled via the
  // IfStmt walk below).
  guard = target
}

/* True if some statement `s` in function `f` is a guard that null-checks
 * the storage referenced by `target` (an expression structurally
 * equivalent to the destination we care about). We match guards
 * syntactically on the *form* of the destination, which is fine for the
 * common one-hop cases (local var, p->field). */
predicate guardsAgainstNull(Function f, Expr destForm) {
  exists(IfStmt ifs, Expr cond, Expr inner |
    ifs.getEnclosingFunction() = f and
    cond = ifs.getCondition() and
    (inner = cond or inner = cond.getAChild*()) and
    isNullCheckExpr(inner, anyAccessEquivalentTo(destForm, f))
  )
  or
  exists(ConditionalExpr ce, Expr cond, Expr inner |
    ce.getEnclosingFunction() = f and
    cond = ce.getCondition() and
    (inner = cond or inner = cond.getAChild*()) and
    isNullCheckExpr(inner, anyAccessEquivalentTo(destForm, f))
  )
}

/* Return any expression in function `f` that is a syntactic re-access
 * of the same storage referenced by `destForm`. Handles VariableAccess
 * (matches by Variable) and PointerFieldAccess (matches by field and
 * qualifier variable). */
Expr anyAccessEquivalentTo(Expr destForm, Function f) {
  // local variable: destForm is a VariableAccess of v
  exists(Variable v |
    destForm.(VariableAccess).getTarget() = v and
    result.(VariableAccess).getTarget() = v and
    result.getEnclosingFunction() = f
  )
  or
  // struct field through pointer: q->fld
  exists(Field fld, Variable q |
    destForm.(PointerFieldAccess).getTarget() = fld and
    destForm.(PointerFieldAccess).getQualifier().(VariableAccess).getTarget() = q and
    result.(PointerFieldAccess).getTarget() = fld and
    result.(PointerFieldAccess).getQualifier().(VariableAccess).getTarget() = q and
    result.getEnclosingFunction() = f
  )
}

/* The destination expression of an assignment `destForm = allocCall`. */
predicate isAllocAssignedTo(FunctionCall allocCall, Expr destForm, Function f) {
  exists(AssignExpr ae |
    ae.getEnclosingFunction() = f and
    ae.getRValue() = allocCall and
    ae.getLValue() = destForm
  ) and
  isAllocator(allocCall.getTarget().getName())
}

/* Any dereference of the same storage referenced by `destForm`:
 *   - dest->field          (PointerFieldAccess where dest is qualifier)
 *   - *dest                (PointerDereferenceExpr)
 *   - dest[i]              (ArrayExpr where dest is the base)
 * `useSite` is the dereferencing expression. */
predicate dereferencesDest(Expr useSite, Expr destForm, Function f) {
  exists(Expr acc | acc = anyAccessEquivalentTo(destForm, f) |
    // p->fld
    exists(PointerFieldAccess pfa |
      pfa = useSite and pfa.getQualifier() = acc
    )
    or
    // *p
    exists(PointerDereferenceExpr pde |
      pde = useSite and pde.getOperand() = acc
    )
    or
    // p[i]
    exists(ArrayExpr ae |
      ae = useSite and ae.getArrayBase() = acc
    )
  ) and
  useSite.getEnclosingFunction() = f
}

from Function f, FunctionCall allocCall, Expr destForm, Expr useSite
where
  // pointer p (or p->fld) is the target of an allocator's return value
  isAllocAssignedTo(allocCall, destForm, f) and
  // somewhere later in the SAME function we dereference that storage
  dereferencesDest(useSite, destForm, f) and
  // the deref is reachable from the allocation (cheap CFG check)
  allocCall.getASuccessor+() = useSite and
  // and lexically follows it
  useSite.getLocation().getStartLine() > allocCall.getLocation().getStartLine() and
  // no NULL guard on that storage anywhere in the function (any guard
  // dominates, because if the developer wrote one it covers the bug)
  not guardsAgainstNull(f, destForm)
select useSite,
  "Pointer from $@ is dereferenced here without a NULL check.",
  allocCall, allocCall.getTarget().getName()
