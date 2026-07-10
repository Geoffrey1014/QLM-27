/**
 * @name Missing NULL check after devm_* allocation
 * @description Detects assignments where a devm_k*alloc result is
 *              stored to a variable/field but the variable is not
 *              subsequently NULL-checked before use. Pattern derived
 *              from commit d6cb77228e3a
 *              (pinctrl: baytrail: Fix potential NULL pointer dereference).
 * @kind problem
 * @problem.severity warning
 * @id qlm/mc-5-rep5-L0
 */

import cpp

predicate isDevmAllocCall(FunctionCall fc) {
  fc.getTarget().getName() in [
    "devm_kcalloc", "devm_kzalloc", "devm_kmalloc", "devm_kmalloc_array",
    "devm_kmemdup", "devm_kstrdup", "devm_kasprintf"
  ]
}

/** Holds if `e` is a syntactic access of the target of assignment `ae`. */
predicate assignsTo(AssignExpr ae, Expr target) { target = ae.getLValue() }

/** Extracts a variable (local or field) that is the LHS of an assignment
 *  whose RHS is (converted from) `alloc`. */
predicate allocAssignedTo(FunctionCall alloc, Variable v) {
  exists(AssignExpr ae |
    ae.getRValue() = alloc.getFullyConverted()
    or ae.getRValue() = alloc
  |
    v.getAnAccess() = ae.getLValue()
    or v = ae.getLValue().(FieldAccess).getTarget()
  )
  or
  exists(Initializer init |
    (init.getExpr() = alloc or init.getExpr() = alloc.getFullyConverted()) and
    init.getDeclaration() = v
  )
}

/** Holds if `guard` is an IfStmt (or return-based guard expression) that
 *  tests `v` for NULL after the allocation site `alloc`. Location-based
 *  ordering: same function, guard start line > alloc start line. */
predicate hasNullCheckAfter(FunctionCall alloc, Variable v) {
  exists(IfStmt guard |
    guard.getEnclosingFunction() = alloc.getEnclosingFunction() and
    guard.getLocation().getStartLine() > alloc.getLocation().getStartLine() and
    guard.getCondition().getAChild*() = v.getAnAccess()
  )
}

from FunctionCall alloc, Variable v
where
  isDevmAllocCall(alloc) and
  allocAssignedTo(alloc, v) and
  not hasNullCheckAfter(alloc, v)
select alloc,
  "Result of devm_* allocation assigned to $@ but no subsequent NULL check was found.",
  v, v.getName()
