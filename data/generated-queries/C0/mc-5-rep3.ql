/**
 * @name Missing NULL check on devm allocator return value
 * @description Functions in the devm_k*alloc / kmalloc family return NULL on
 *              allocation failure. Storing the returned pointer (for example
 *              into a struct field) without checking for NULL before
 *              dereferencing or otherwise using it later can cause a NULL
 *              pointer dereference. This query flags assignments of a devm
 *              allocator result to a field/variable where there is no NULL
 *              check (no guard) on that result anywhere in the enclosing
 *              function.
 * @kind problem
 * @problem.severity warning
 * @id cpp/missing-null-check-devm-alloc
 * @tags reliability
 *       correctness
 *       security
 */

import cpp
import semmle.code.cpp.controlflow.Guards

/**
 * Allocator functions whose return value is a pointer that is NULL on
 * failure. We focus on the devm_* family (managed allocations used
 * pervasively in driver probe paths) plus the closely related kmalloc
 * family that shares the same NULL-on-failure contract.
 */
predicate isNullableAllocator(Function f) {
  exists(string n | n = f.getName() |
    n = "devm_kmalloc" or
    n = "devm_kzalloc" or
    n = "devm_kcalloc" or
    n = "devm_kmalloc_array" or
    n = "devm_krealloc" or
    n = "devm_kmemdup" or
    n = "devm_kstrdup" or
    n = "devm_kasprintf" or
    n = "kmalloc" or
    n = "kzalloc" or
    n = "kcalloc" or
    n = "kmalloc_array" or
    n = "krealloc" or
    n = "kmemdup" or
    n = "kstrdup" or
    n = "vmalloc" or
    n = "vzalloc" or
    n = "kvmalloc" or
    n = "kvzalloc"
  )
}

/**
 * Holds if `e` is, syntactically, a check of `target` against NULL
 * (or a logical-not / IS_ERR style use of it). We approximate by
 * looking for any expression inside an `if`/`while`/`?:` condition
 * that references the same variable/field as `target`.
 */
predicate isCheckedAgainstNull(Expr target, Function enclosing) {
  exists(IfStmt ifs, Expr cond |
    ifs.getEnclosingFunction() = enclosing and
    cond = ifs.getCondition() and
    referencesSameStorage(cond, target)
  )
  or
  exists(ConditionalExpr ce |
    ce.getEnclosingFunction() = enclosing and
    referencesSameStorage(ce.getCondition(), target)
  )
  or
  exists(Loop l, Expr cond |
    l.getEnclosingFunction() = enclosing and
    cond = l.getCondition() and
    referencesSameStorage(cond, target)
  )
}

/**
 * Holds if `check` references the same underlying storage location
 * as `target`. We handle the common cases:
 *   - both are accesses to the same local variable
 *   - both are field accesses to the same field on the same qualifier
 */
predicate referencesSameStorage(Expr check, Expr target) {
  exists(VariableAccess va1, VariableAccess va2 |
    va1 = check.getAChild*() and
    va2 = target and
    va1.getTarget() = va2.getTarget()
  )
  or
  exists(FieldAccess fa1, FieldAccess fa2 |
    fa1 = check.getAChild*() and
    fa2 = target and
    fa1.getTarget() = fa2.getTarget()
  )
}

/**
 * The LHS of an assignment whose RHS is a call to a nullable allocator,
 * paired with the call.
 */
predicate assignsFromAllocator(Expr lhs, FunctionCall fc) {
  exists(AssignExpr ae |
    ae.getRValue() = fc and
    lhs = ae.getLValue() and
    isNullableAllocator(fc.getTarget())
  )
}

from FunctionCall fc, Expr lhs, Function caller
where
  isNullableAllocator(fc.getTarget()) and
  caller = fc.getEnclosingFunction() and
  assignsFromAllocator(lhs, fc) and
  not isCheckedAgainstNull(lhs, caller) and
  // Heuristic: only flag when the LHS is something whose later use
  // could plausibly dereference it (field on a struct pointer or a
  // local pointer variable).
  (lhs instanceof FieldAccess or lhs instanceof VariableAccess)
select fc,
  "Return value of " + fc.getTarget().getName() +
    "() is stored without a NULL check; the pointer may be dereferenced later " +
    "even though allocation can fail."
