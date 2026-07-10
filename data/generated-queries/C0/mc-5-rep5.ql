/**
 * @name Missing NULL check after devm_k*alloc allocation
 * @description An allocation function from the devm_k*alloc family (devm_kmalloc,
 *              devm_kzalloc, devm_kcalloc, devm_kmalloc_array, devm_kmemdup, etc.)
 *              can return NULL on failure. The returned pointer must be checked
 *              for NULL before being dereferenced or passed to a function that
 *              dereferences it. Missing such a check can cause a NULL pointer
 *              dereference. This generalises the pattern fixed by adding
 *              `if (!ptr) return -ENOMEM;` after a devm_kcalloc() call.
 * @kind problem
 * @problem.severity warning
 * @id cpp/missing-null-check-devm-alloc
 * @tags reliability
 *       correctness
 *       security
 */

import cpp
import semmle.code.cpp.controlflow.Guards
import semmle.code.cpp.controlflow.ControlFlowGraph

/**
 * The family of devm_k*alloc allocator names whose return value can be NULL
 * on failure and therefore must be NULL-checked before use.
 */
predicate isDevmAllocName(string name) {
  name = "devm_kmalloc" or
  name = "devm_kzalloc" or
  name = "devm_kcalloc" or
  name = "devm_kmalloc_array" or
  name = "devm_kzalloc_array" or
  name = "devm_kmemdup" or
  name = "devm_krealloc" or
  name = "devm_kstrdup" or
  name = "devm_kstrndup" or
  name = "devm_kasprintf" or
  name = "devm_kvasprintf"
}

/** A call to a devm_k*alloc-family allocator. */
class DevmAllocCall extends FunctionCall {
  DevmAllocCall() { isDevmAllocName(this.getTarget().getName()) }
}

/**
 * Holds if `e` is an expression that (syntactically) tests `v` against NULL,
 * either directly (`!v`, `v == NULL`, `v != NULL`, `v` used as a boolean) or
 * inside the controlling expression of an if/while/for/?:.
 */
predicate nullChecks(Expr e, Variable v) {
  // e is a direct access to v inside a guard / logical context
  exists(VariableAccess va | va = v.getAnAccess() |
    e = va
    or
    e.(NotExpr).getOperand() = va
    or
    e.(EQExpr).getAnOperand() = va and e.(EQExpr).getAnOperand().getValue() = "0"
    or
    e.(NEExpr).getAnOperand() = va and e.(NEExpr).getAnOperand().getValue() = "0"
  )
}

/**
 * Holds if some guard condition on a control-flow path dominating `use`
 * tests `v` for NULL.
 */
predicate hasNullGuard(Variable v, Expr use) {
  exists(GuardCondition g, BasicBlock bb |
    bb = use.getBasicBlock() and
    g.controls(bb, _) and
    nullChecks(g, v)
  )
  or
  // Fallback: any check syntactically before the use in the same function.
  exists(Expr check, ControlFlowNode checkNode, ControlFlowNode useNode |
    nullChecks(check, v) and
    checkNode = check and
    useNode = use and
    check.getEnclosingFunction() = use.getEnclosingFunction() and
    checkNode.getASuccessor+() = useNode
  )
}

/**
 * A use of `v` that involves an actual dereference (field access through ->,
 * array indexing, pointer dereference, or pass-by-value of a struct field).
 */
predicate isDereferenceUse(VariableAccess va, Variable v) {
  va = v.getAnAccess() and
  (
    exists(PointerFieldAccess pfa | pfa.getQualifier() = va)
    or
    exists(ArrayExpr ae | ae.getArrayBase() = va)
    or
    exists(PointerDereferenceExpr pde | pde.getOperand() = va)
    or
    exists(Assignment a | a.getLValue().(PointerFieldAccess).getQualifier() = va)
  )
}

from DevmAllocCall alloc, Variable v, VariableAccess derefUse, Function f
where
  f = alloc.getEnclosingFunction() and
  // v is assigned the result of the alloc, either by local-var init or by
  // a plain assignment (covers `x = devm_kcalloc(...)` and `T *x = devm_kcalloc(...)`).
  (
    exists(AssignExpr a |
      a.getRValue() = alloc and
      a.getLValue() = v.getAnAccess()
    )
    or
    exists(Initializer init |
      init.getExpr() = alloc and
      init.getDeclaration() = v
    )
    or
    // Field assignment: vg->saved_context = devm_kcalloc(...).
    exists(AssignExpr a, FieldAccess fa |
      a.getRValue() = alloc and
      a.getLValue() = fa and
      fa.getTarget() = v
    )
  ) and
  isDereferenceUse(derefUse, v) and
  derefUse.getEnclosingFunction() = f and
  // The dereference is reachable from the allocation in the CFG.
  alloc.(ControlFlowNode).getASuccessor+() = derefUse and
  // And there is no NULL guard on v that controls (or precedes) the dereference.
  not hasNullGuard(v, derefUse)
select alloc,
  "Result of " + alloc.getTarget().getName() +
    "() is assigned to '" + v.getName() +
    "' and later dereferenced at $@ without a NULL check.",
  derefUse, derefUse.toString()
