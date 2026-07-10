/**
 * @name  rq3-c2-mc-2-rep1
 * @id    cpp/rq3/c2/mc-2-rep1
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects allocations (kzalloc/kmalloc/kcalloc/etc.) whose return value
 *              is stored but never null-checked before being dereferenced/used.
 */

import cpp
import semmle.code.cpp.controlflow.Guards

/* P1: the call is to a kernel allocator that can return NULL on failure. */
predicate is_alloc_call(FunctionCall fc) {
  exists(string n | n = fc.getTarget().getName() |
    n = "kzalloc" or
    n = "kmalloc" or
    n = "kcalloc" or
    n = "kmalloc_array" or
    n = "kzalloc_node" or
    n = "kmalloc_node" or
    n = "vmalloc" or
    n = "vzalloc" or
    n = "devm_kzalloc" or
    n = "devm_kmalloc"
  )
}

/* P2: the call's return value is stored into some lvalue (a local var, or a field). */
predicate alloc_result_stored(FunctionCall fc, Expr lhs) {
  exists(AssignExpr ae | ae.getRValue() = fc and ae.getLValue() = lhs)
  or
  exists(Initializer init | init.getExpr() = fc and lhs = init.getDeclaration().(Variable).getAnAccess())
}

/* P3: there exists a guard (if statement / conditional) whose condition mentions the
 *     allocated lvalue and that dominates a subsequent use — i.e., the lvalue is
 *     null-checked somewhere after the allocation. */
predicate alloc_null_checked(FunctionCall fc) {
  exists(Expr lhs, GuardCondition gc, Expr ref |
    alloc_result_stored(fc, lhs) and
    ref = lhsRefLikely(lhs) and
    ref.getParent+() = gc
  )
}

/* helper: another access to the same variable/field as lhs */
Expr lhsRefLikely(Expr lhs) {
  exists(Variable v |
    lhs = v.getAnAccess() and result = v.getAnAccess()
  )
  or
  exists(Field f |
    lhs.(FieldAccess).getTarget() = f and
    result.(FieldAccess).getTarget() = f
  )
}

/* P4: an unchecked allocation = stored result, but no null check seen on it. */
predicate unchecked_alloc(FunctionCall fc) {
  is_alloc_call(fc) and
  exists(Expr lhs | alloc_result_stored(fc, lhs)) and
  not alloc_null_checked(fc)
}

from FunctionCall fc
where unchecked_alloc(fc)
select fc, "Allocation result from " + fc.getTarget().getName() + " is not null-checked before use."
