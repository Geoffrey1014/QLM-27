/**
 * @name Missing NULL check after kernel allocator call
 * @description An allocator call (kzalloc/kmalloc/kcalloc/etc.) whose result
 *              is stored into a variable without any subsequent NULL check on
 *              that variable, matching commit 09acf29c8246.
 * @kind problem
 * @problem.severity warning
 * @id qlm/missing-null-check-after-alloc
 */

import cpp

predicate isAllocCall(FunctionCall fc) {
  fc.getTarget().getName() in [
    "kzalloc", "kmalloc", "kcalloc", "kzalloc_node",
    "kmalloc_array", "vzalloc", "vmalloc",
    "devm_kzalloc", "devm_kmalloc"
  ]
}

predicate hasNullCheckAfter(FunctionCall fc) {
  exists(Variable v, Expr check |
    (fc = v.getAnAssignedValue() or fc.getParent() = v.getAnAssignedValue()) and
    check.getEnclosingFunction() = fc.getEnclosingFunction() and
    check.getAChild*() = v.getAnAccess() and
    (check instanceof EqualityOperation or check instanceof NotExpr) and
    check.getLocation().getStartLine() > fc.getLocation().getStartLine()
  )
}

from FunctionCall fc
where isAllocCall(fc) and not hasNullCheckAfter(fc)
select fc, "Missing NULL check after allocator call."
