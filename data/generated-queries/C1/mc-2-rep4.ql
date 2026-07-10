/**
 * @name Missing NULL check after allocator returning a pointer (kzalloc / kmalloc / kcalloc family)
 * @description An allocator (e.g. kzalloc) result is stored and then control
 *              continues without checking the assigned target for NULL before
 *              the function returns or the object is used further.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-mc-2
 */

import cpp

/** Holds if `f` is a kernel-style allocator that may return NULL. */
predicate isAllocator(Function f) {
  f.getName()
      .regexpMatch("k[mz]alloc|kcalloc|kmalloc_array|kzalloc_node|kmalloc_node|kvmalloc|kvzalloc|vmalloc|vzalloc|devm_kzalloc|devm_kmalloc")
}

/** A call to an allocator. */
class AllocCall extends FunctionCall {
  AllocCall() { isAllocator(this.getTarget()) }
}

/**
 * Holds if `e` is (or contains) a NULL-check on something whose string form
 * matches `targetStr` (e.g. `!priv->pFirmware`, `priv->pFirmware == NULL`).
 */
predicate exprIsNullCheckOn(Expr e, string targetStr) {
  (
    exists(NotExpr ne | ne = e and ne.getOperand().toString() = targetStr)
    or
    exists(EQExpr eq | eq = e |
      (eq.getLeftOperand().toString() = targetStr and eq.getRightOperand().getValue() = "0")
      or
      (eq.getRightOperand().toString() = targetStr and eq.getLeftOperand().getValue() = "0")
    )
  )
  or
  exists(Expr sub | sub.getParent+() = e and exprIsNullCheckOn(sub, targetStr))
}

/**
 * Holds if function `f` contains some `IfStmt` whose condition is a NULL-check
 * on something stringifying as `targetStr`, and the if-statement's line is at or
 * after `assignLine` (the line of the allocation assignment).
 */
predicate hasNullCheckSomewhere(Function f, string targetStr) {
  exists(IfStmt ifs |
    ifs.getEnclosingFunction() = f and
    exprIsNullCheckOn(ifs.getCondition(), targetStr)
  )
}

from AssignExpr assign, AllocCall alloc, Expr target, Function f, string targetStr
where
  f = assign.getEnclosingFunction() and
  assign.getRValue() = alloc and
  target = assign.getLValue() and
  targetStr = target.toString() and
  not hasNullCheckSomewhere(f, targetStr)
select assign,
  "Missing NULL check: result of allocator '" + alloc.getTarget().getName() +
  "' assigned to '" + targetStr + "' is used without a NULL check before subsequent use."
