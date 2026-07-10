/**
 * @name Missing NULL check after devm_kcalloc / kmalloc-family allocation (L0)
 * @description Detects allocator calls (devm_kcalloc, devm_kzalloc, kmalloc,
 *              kzalloc, kcalloc, devm_kmalloc) whose pointer result is
 *              stored into a struct field and subsequently read downstream
 *              in the same function without an intervening NULL check on
 *              that field. Pattern derived from upstream commit
 *              d6cb77228e3a ("pinctrl: baytrail: Fix potential NULL pointer
 *              dereference").
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3/l0/mc-5/missing-null-check-after-alloc
 * @tags reliability
 *       missing-check
 *       CWE-476
 */

import cpp

/* Single L0 predicate — folds allocator recognition, field-assignment,
 * downstream field-read, and missing-null-check into one conjunction. */
predicate allocFieldUnchecked(FunctionCall allocCall, FieldAccess target) {
  allocCall.getTarget().getName() in
    ["devm_kcalloc", "devm_kzalloc", "devm_kmalloc",
     "kmalloc", "kzalloc", "kcalloc"] and
  exists(Assignment a |
    a.getRValue() = allocCall and
    a.getLValue() = target
  ) and
  exists(FieldAccess use |
    use.getQualifier().toString() = target.getQualifier().toString() and
    use.getTarget() = target.getTarget() and
    use.getLocation().getStartLine() > allocCall.getLocation().getStartLine() and
    use.getEnclosingFunction() = allocCall.getEnclosingFunction() and
    not exists(Assignment aw | aw.getLValue() = use)
  ) and
  not exists(IfStmt ifs, FieldAccess fa |
    fa = ifs.getCondition().getAChild*() and
    fa.getQualifier().toString() = target.getQualifier().toString() and
    fa.getTarget() = target.getTarget() and
    ifs.getLocation().getStartLine() > allocCall.getLocation().getStartLine() and
    ifs.getEnclosingFunction() = allocCall.getEnclosingFunction()
  )
}

from FunctionCall allocCall, FieldAccess target
where allocFieldUnchecked(allocCall, target)
select allocCall,
       "Missing NULL check after allocation; field '" + target.toString() +
       "' is consumed downstream without guard in " +
       allocCall.getEnclosingFunction().getName() + " (CWE-476)"
