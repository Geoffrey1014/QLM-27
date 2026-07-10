/**
 * @name Missing NULL check after kzalloc/kmalloc family allocation
 * @description An allocation function from the kmalloc family (kmalloc, kzalloc,
 *              kcalloc, kmalloc_array, kzalloc_node, vmalloc, vzalloc, etc.)
 *              may return NULL on failure. Dereferencing or storing into the
 *              returned pointer without first checking for NULL leads to a
 *              NULL-pointer dereference. The fix pattern (e.g. commit
 *              09acf29c8246 in drivers/staging/rtl8192u/r8192U_core.c) is to
 *              add an `if (!p) return -ENOMEM;` immediately after the call.
 * @kind problem
 * @problem.severity error
 * @id cpp/linux-kmalloc-missing-null-check
 * @tags reliability
 *       security
 *       external/cwe/cwe-476
 */

import cpp
import semmle.code.cpp.controlflow.Guards
import semmle.code.cpp.controlflow.ControlFlowGraph

/** Holds if `name` is a kernel allocation function whose result may be NULL. */
predicate isAllocFuncName(string name) {
  name = "kmalloc" or
  name = "kzalloc" or
  name = "kcalloc" or
  name = "kmalloc_array" or
  name = "kmalloc_node" or
  name = "kzalloc_node" or
  name = "kmalloc_array_node" or
  name = "kcalloc_node" or
  name = "kmemdup" or
  name = "kstrdup" or
  name = "kstrndup" or
  name = "vmalloc" or
  name = "vzalloc" or
  name = "vmalloc_node" or
  name = "vzalloc_node" or
  name = "kvmalloc" or
  name = "kvzalloc" or
  name = "kvmalloc_node" or
  name = "kvcalloc" or
  name = "devm_kmalloc" or
  name = "devm_kzalloc" or
  name = "devm_kcalloc"
}

/** A call to a kmalloc-family allocator. */
class AllocCall extends FunctionCall {
  AllocCall() { isAllocFuncName(this.getTarget().getName()) }
}

/**
 * Holds if `e` is a NULL-check on expression `checked` (directly or via `!`,
 * `== NULL`, `!= NULL`, or used as a guard condition).
 */
predicate isNullCheckOn(Expr guardExpr, Expr checked) {
  // !p
  exists(NotExpr ne | ne = guardExpr and ne.getOperand() = checked)
  or
  // p == NULL  /  p == 0  /  NULL == p
  exists(EQExpr eq | eq = guardExpr |
    (eq.getLeftOperand() = checked and eq.getRightOperand().getValue() = "0") or
    (eq.getRightOperand() = checked and eq.getLeftOperand().getValue() = "0")
  )
  or
  // p != NULL
  exists(NEExpr ne | ne = guardExpr |
    (ne.getLeftOperand() = checked and ne.getRightOperand().getValue() = "0") or
    (ne.getRightOperand() = checked and ne.getLeftOperand().getValue() = "0")
  )
  or
  // if (p) ...  — bare use as condition (the variable access itself is the guard)
  checked = guardExpr
}

/**
 * Holds if the result of `alloc` (assigned into variable access `target`) is
 * NULL-checked anywhere in the enclosing function.
 */
predicate hasNullCheck(AllocCall alloc, Variable v) {
  exists(Expr g, VariableAccess va |
    va.getTarget() = v and
    va.getEnclosingFunction() = alloc.getEnclosingFunction() and
    isNullCheckOn(g, va) and
    // The check appears in some guard / if-condition somewhere
    (
      exists(IfStmt ifs | ifs.getCondition() = g or ifs.getCondition().getAChild*() = g)
      or
      exists(ConditionalExpr ce | ce.getCondition() = g or ce.getCondition().getAChild*() = g)
      or
      exists(LogicalAndExpr la | la.getAnOperand() = g or la.getAnOperand().getAChild*() = g)
      or
      exists(LogicalOrExpr lo | lo.getAnOperand() = g or lo.getAnOperand().getAChild*() = g)
    )
  )
}

/**
 * Holds if the allocation result is stored into `v` (either via assignment or
 * variable initializer / struct-field store).
 */
predicate allocAssignedToVar(AllocCall alloc, Variable v) {
  // int *p = kmalloc(...);
  exists(Initializer init | init.getExpr() = alloc and init.getDeclaration() = v)
  or
  // p = kmalloc(...);
  exists(AssignExpr ae | ae.getRValue() = alloc and ae.getLValue().(VariableAccess).getTarget() = v)
}

/**
 * Holds if the allocated pointer (held in `v`) is subsequently used in a way
 * that would crash on NULL: dereferenced, used as a struct base, or passed
 * to a function that will dereference it (e.g. memcpy, memset).
 */
predicate isUsedDangerously(AllocCall alloc, Variable v) {
  exists(VariableAccess va |
    va.getTarget() = v and
    va.getEnclosingFunction() = alloc.getEnclosingFunction() and
    (
      // *p   or   p->field   or   p[i]
      exists(PointerDereferenceExpr d | d.getOperand() = va) or
      exists(PointerFieldAccess pfa | pfa.getQualifier() = va) or
      exists(ArrayExpr ae | ae.getArrayBase() = va)
    )
  )
}

from AllocCall alloc, Variable v
where
  allocAssignedToVar(alloc, v) and
  isUsedDangerously(alloc, v) and
  not hasNullCheck(alloc, v) and
  // Reduce noise from generated / non-kernel test code
  not alloc.getFile().getAbsolutePath().matches("%/tools/%")
select alloc,
  "Result of " + alloc.getTarget().getName() +
    "() stored into '" + v.getName() +
    "' is dereferenced without a NULL check, risking a NULL-pointer dereference."
