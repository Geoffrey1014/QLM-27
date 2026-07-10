/**
 * @name Missing NULL check after devm_kcalloc / kmalloc-family allocation
 * @description Detects allocator calls (devm_kcalloc, devm_kzalloc, kmalloc,
 *              kzalloc, kcalloc, devm_kmalloc) whose pointer result is
 *              stored into a struct field and subsequently read downstream
 *              in the same function without an intervening NULL check on
 *              that field. Pattern derived from upstream commit
 *              d6cb77228e3a ("pinctrl: baytrail: Fix potential NULL pointer
 *              dereference").
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3/c3/missing-null-check-after-alloc
 * @tags reliability
 *       missing-check
 *       CWE-476
 */

import cpp

/* P1: allocator APIs whose return value may be NULL on failure. */
predicate isAllocApi(FunctionCall fc) {
  fc.getTarget().getName() in
    ["devm_kcalloc", "devm_kzalloc", "devm_kmalloc",
     "kmalloc", "kzalloc", "kcalloc"]
}

/* P2: the allocator's result is assigned to a struct field. */
predicate allocResultStoredInField(FunctionCall fc, Expr target) {
  isAllocApi(fc) and
  exists(Assignment a |
    a.getRValue() = fc and
    a.getLValue() = target and
    target instanceof FieldAccess
  )
}

/* P3: somewhere later in the same function, an if-statement guards on
 *     the SAME struct field that received the alloc result (NULL check). */
predicate hasNullCheckOnTarget(FunctionCall allocCall, Expr target) {
  allocResultStoredInField(allocCall, target) and
  exists(IfStmt ifs, FieldAccess fa |
    fa = ifs.getCondition().getAChild*() and
    fa.getQualifier().toString() = target.(FieldAccess).getQualifier().toString() and
    fa.getTarget() = target.(FieldAccess).getTarget() and
    ifs.getLocation().getStartLine() > allocCall.getLocation().getStartLine() and
    ifs.getEnclosingFunction() = allocCall.getEnclosingFunction()
  )
}

/* P4: that same field is READ (not written) at some later point in the
 *     same enclosing function — proxy for "downstream dereference". */
predicate downstreamUsesTarget(FunctionCall allocCall, Expr target) {
  allocResultStoredInField(allocCall, target) and
  exists(FieldAccess use |
    use.getQualifier().toString() = target.(FieldAccess).getQualifier().toString() and
    use.getTarget() = target.(FieldAccess).getTarget() and
    use.getLocation().getStartLine() > allocCall.getLocation().getStartLine() and
    use.getEnclosingFunction() = allocCall.getEnclosingFunction() and
    not exists(Assignment a | a.getLValue() = use)
  )
}

from FunctionCall allocCall, Expr target
where
  isAllocApi(allocCall) and
  allocResultStoredInField(allocCall, target) and
  downstreamUsesTarget(allocCall, target) and
  not hasNullCheckOnTarget(allocCall, target)
select allocCall,
       "Missing NULL check after allocation; field is consumed downstream " +
       "without guard in " + allocCall.getEnclosingFunction().getName() +
       " (CWE-476)"
