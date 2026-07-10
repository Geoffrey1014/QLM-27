/**
 * @name Missing NULL check after devm_k*alloc family allocation
 * @description Allocations from the devm_kmalloc / devm_kzalloc / devm_kcalloc / devm_kmemdup /
 *              devm_kasprintf family may return NULL on failure. Using the returned pointer
 *              without a NULL check before storing it into a long-lived structure (or
 *              dereferencing it later) can lead to a NULL pointer dereference. This
 *              query reports devm_k*alloc call results that flow to a dereference or to
 *              a field-store without an intervening NULL check.
 * @kind problem
 * @problem.severity warning
 * @id cpp/missing-null-check-devm-kalloc
 * @tags reliability
 *       correctness
 *       security
 */

import cpp
import semmle.code.cpp.controlflow.Guards
import semmle.code.cpp.dataflow.DataFlow

/**
 * The family of devm_* allocation functions whose return value can be NULL on failure.
 * Generalized beyond `devm_kcalloc` (the specific API in the seed patch) to cover
 * sibling allocators in the same family.
 */
class DevmAllocFunction extends Function {
  DevmAllocFunction() {
    this.getName() =
      [
        "devm_kmalloc", "devm_kzalloc", "devm_kcalloc", "devm_kmalloc_array",
        "devm_kmemdup", "devm_kstrdup", "devm_kstrdup_const", "devm_kasprintf",
        "devm_kvasprintf", "devm_kvcalloc", "devm_kvzalloc", "devm_kvmalloc",
        "devm_kvmalloc_array"
      ]
  }
}

/** A call to a devm_* allocator. */
class DevmAllocCall extends FunctionCall {
  DevmAllocCall() { this.getTarget() instanceof DevmAllocFunction }
}

/**
 * Holds if `e` is a NULL-ness check (directly or via logical negation) on the
 * value of `v` somewhere in the function. We approximate the "no NULL check"
 * condition by requiring NO guard mentioning `v` compared against 0/NULL.
 */
predicate hasNullCheckOn(Variable v) {
  exists(GuardCondition g, VariableAccess va |
    va = v.getAnAccess() and
    (
      g = va or
      g.(NotExpr).getOperand() = va or
      g.(EqualityOperation).getAnOperand() = va or
      g.(EqualityOperation).getAnOperand().(Expr) = va
    )
  )
  or
  exists(IfStmt is, VariableAccess va |
    va = v.getAnAccess() and
    va.getEnclosingStmt().getParentStmt*() = is.getCondition().getEnclosingStmt() and
    (
      is.getCondition() = va or
      is.getCondition().(NotExpr).getOperand() = va or
      is.getCondition().(EqualityOperation).getAnOperand() = va
    )
  )
}

/** A dereference of an expression (pointer deref, field access through pointer, array index). */
predicate isDereference(Expr e) {
  exists(PointerDereferenceExpr pde | pde.getOperand() = e)
  or
  exists(PointerFieldAccess pfa | pfa.getQualifier() = e)
  or
  exists(ArrayExpr ae | ae.getArrayBase() = e)
}

/**
 * Holds if the result of `call` flows (intraprocedurally) to a dereference
 * or to a field-store that treats it as a valid pointer.
 */
predicate flowsToUnsafeUse(DevmAllocCall call, Expr useSite) {
  exists(DataFlow::Node src, DataFlow::Node sink |
    src.asExpr() = call and
    sink.asExpr() = useSite and
    DataFlow::localFlow(src, sink) and
    (
      isDereference(useSite)
      or
      // assignment of allocator result into a struct field, then later code in same function
      // dereferences the same source value
      exists(Assignment a | a.getRValue() = useSite and a.getLValue() instanceof FieldAccess)
    )
  )
}

/**
 * Holds if `call`'s return value is assigned to variable `v` and `v` is not
 * subsequently NULL-checked before being used.
 */
predicate assignedWithoutCheck(DevmAllocCall call, Variable v) {
  exists(Assignment a |
    a.getRValue() = call and
    (
      a.getLValue() = v.getAnAccess()
      or
      a.getLValue().(FieldAccess).getTarget() = v
    )
  ) and
  not hasNullCheckOn(v)
}

from DevmAllocCall call, Function enclosing
where
  enclosing = call.getEnclosingFunction() and
  // No NULL-check guard anywhere in the enclosing function that mentions
  // a variable that was assigned from `call`.
  (
    exists(Variable v | assignedWithoutCheck(call, v))
    or
    exists(Expr useSite |
      flowsToUnsafeUse(call, useSite) and
      useSite != call
    )
  )
select call,
  "Result of devm_* allocator '" + call.getTarget().getName() +
    "' may be NULL but appears to be used without a NULL check in function '" +
    enclosing.getName() + "'."
