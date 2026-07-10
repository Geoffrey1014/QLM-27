/**
 * @name Missing NULL check after devm_kcalloc / kmalloc-family allocation
 * @description Detects calls to devm_kcalloc / devm_kzalloc / kmalloc /
 *              kzalloc / kcalloc whose return value is stored into a target
 *              (struct field or local) that is then used downstream in the
 *              same enclosing function without an intervening NULL check on
 *              that target. Pattern derived from upstream commit
 *              d6cb77228e3a ("pinctrl: baytrail: Fix potential NULL pointer
 *              dereference").
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3/c3/missing-null-check-after-alloc
 * @tags reliability
 *       missing-check
 *       null-pointer
 */

import cpp

/* P1: target alloc-style APIs whose return is a heap pointer that may be NULL. */
predicate isAllocApi(FunctionCall fc) {
  fc.getTarget().getName() = "devm_kcalloc" or
  fc.getTarget().getName() = "devm_kzalloc" or
  fc.getTarget().getName() = "devm_kmalloc" or
  fc.getTarget().getName() = "kmalloc" or
  fc.getTarget().getName() = "kzalloc" or
  fc.getTarget().getName() = "kcalloc"
}

/* P2: lvalue (field-access or local) that the allocation's return is stored
 *     into. We accept both `x = alloc(...);` and `T *x = alloc(...);` shapes. */
Expr getAllocatedTarget(FunctionCall alloc) {
  exists(AssignExpr a | a.getRValue() = alloc and result = a.getLValue())
  or
  exists(Variable v |
    v.getInitializer().getExpr() = alloc and
    result.(VariableAccess).getTarget() = v and
    result.getEnclosingFunction() = alloc.getEnclosingFunction())
}

/* P3: at or after the allocation, in the same enclosing function, some
 *     IfStmt / ConditionalExpr's condition references the target by name. */
predicate hasNullCheckBetween(FunctionCall alloc, Expr target) {
  exists(IfStmt ifs |
    ifs.getEnclosingFunction() = alloc.getEnclosingFunction() and
    ifs.getLocation().getStartLine() >= alloc.getLocation().getStartLine() and
    ifs.getCondition().getAChild*().toString() = target.toString())
  or
  exists(ConditionalExpr ce |
    ce.getEnclosingFunction() = alloc.getEnclosingFunction() and
    ce.getLocation().getStartLine() >= alloc.getLocation().getStartLine() and
    ce.getCondition().getAChild*().toString() = target.toString())
}

/* P4: after the allocation, in the same enclosing function, either the
 *     target appears again in an expression, or a known downstream consumer
 *     call sees the containing struct (modeling cross-procedural deref). */
predicate isUsedDownstream(FunctionCall alloc, Expr target) {
  exists(Expr use |
    use.getEnclosingFunction() = alloc.getEnclosingFunction() and
    use.getLocation().getStartLine() > alloc.getLocation().getStartLine() and
    use.toString() = target.toString())
  or
  exists(FunctionCall downstream |
    downstream.getEnclosingFunction() = alloc.getEnclosingFunction() and
    downstream.getLocation().getStartLine() > alloc.getLocation().getStartLine() and
    (downstream.getTarget().getName() = "consume_ctx" or
     downstream.getTarget().getName() = "consume_void" or
     downstream.getTarget().getName() = "devm_gpiochip_add_data"))
}

from FunctionCall alloc, Expr target
where
  isAllocApi(alloc) and
  target = getAllocatedTarget(alloc) and
  isUsedDownstream(alloc, target) and
  not hasNullCheckBetween(alloc, target)
select alloc,
       "Allocation result stored into '" + target.toString() +
       "' is used downstream in " + alloc.getEnclosingFunction().getName() +
       " without an intervening NULL check (missing-check after alloc)"
