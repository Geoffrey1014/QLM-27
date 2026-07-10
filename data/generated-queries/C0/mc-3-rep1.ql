/**
 * @name Pointer dereferenced before NULL check
 * @description A pointer parameter or variable is dereferenced before it is checked
 *              against NULL on the same execution path. Either the NULL check is
 *              redundant (the deref would already have crashed) or, more importantly,
 *              the deref is a latent NULL-pointer dereference bug. Detects the class
 *              of bugs fixed by commits that move a `if (!p) return -EINVAL;` check
 *              ahead of the first `p->member` use, or replace a `BUG_ON(!p)` placed
 *              after a deref with an early return.
 * @kind problem
 * @problem.severity error
 * @id cpp/deref-before-null-check
 * @tags reliability
 *       correctness
 *       security
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph

/**
 * Holds if `e` is an expression whose evaluation dereferences `v`
 * (either via `v->...`, `*v`, `v[i]`, or by taking `&v->field`).
 */
predicate dereferencesVar(Expr e, Variable v) {
  exists(PointerFieldAccess pfa |
    pfa = e and pfa.getQualifier() = v.getAnAccess()
  )
  or
  exists(PointerDereferenceExpr pde |
    pde = e and pde.getOperand() = v.getAnAccess()
  )
  or
  exists(ArrayExpr ae |
    ae = e and ae.getArrayBase() = v.getAnAccess()
  )
  or
  // &rfkill->dev  — the AddressOfExpr's operand is itself a field access
  // that dereferences v.
  exists(AddressOfExpr aoe, PointerFieldAccess pfa |
    aoe = e and aoe.getOperand() = pfa and pfa.getQualifier() = v.getAnAccess()
  )
}

/**
 * Holds if `check` is a NULL-check on variable `v`, i.e. a comparison
 * to a null pointer constant or a logical-not on `v`.
 */
predicate isNullCheckOf(Expr check, Variable v) {
  // if (!v) ...
  exists(NotExpr ne |
    ne = check and ne.getOperand() = v.getAnAccess()
  )
  or
  // if (v == NULL) / if (v != NULL)
  exists(EqualityOperation eq |
    eq = check and
    eq.getAnOperand() = v.getAnAccess() and
    eq.getAnOperand().getValue() = "0"
  )
  or
  // BUG_ON(!v) — BUG_ON is a macro; its expansion contains a NotExpr
  // on v. We capture the NotExpr directly above.
  exists(MacroInvocation mi |
    mi.getMacroName() = "BUG_ON" and
    mi.getAnExpandedElement() = check.(NotExpr) and
    check.(NotExpr).getOperand() = v.getAnAccess()
  )
}

/**
 * Holds if `check` syntactically null-checks `v` and is the controlling
 * expression of an if-statement, or appears inside a BUG_ON / WARN_ON
 * style macro.
 */
predicate isGuardingNullCheck(Expr check, Variable v) {
  isNullCheckOf(check, v) and
  (
    exists(IfStmt is | is.getCondition() = check.getParent*())
    or
    exists(MacroInvocation mi |
      mi.getMacroName() in ["BUG_ON", "WARN_ON", "WARN_ON_ONCE", "VM_BUG_ON"] and
      mi.getAnExpandedElement() = check
    )
  )
}

/**
 * Holds if `derefNode` and `checkNode` are CFG nodes in the same function,
 * `derefNode` is reachable to `checkNode` via successor edges, and there is
 * no assignment to `v` between them.
 */
predicate derefBeforeCheck(
  ControlFlowNode derefNode, Expr derefExpr,
  ControlFlowNode checkNode, Expr checkExpr,
  Variable v, Function f
) {
  dereferencesVar(derefExpr, v) and
  derefNode = derefExpr and
  derefNode.getControlFlowScope() = f and
  isGuardingNullCheck(checkExpr, v) and
  checkNode = checkExpr and
  checkNode.getControlFlowScope() = f and
  derefNode.getASuccessor+() = checkNode and
  // Restrict to parameters or locals — exclude fields/globals where a
  // re-assignment between deref and check could happen out-of-scope.
  (v instanceof Parameter or v instanceof LocalVariable) and
  // No write to v between the deref and the check.
  not exists(ControlFlowNode mid, Assignment a |
    a = mid and
    a.getLValue() = v.getAnAccess() and
    derefNode.getASuccessor+() = mid and
    mid.getASuccessor+() = checkNode
  ) and
  // Both nodes must be in the same function body.
  derefExpr.getEnclosingFunction() = f and
  checkExpr.getEnclosingFunction() = f
}

from
  Function f, Variable v, ControlFlowNode derefNode, Expr derefExpr,
  ControlFlowNode checkNode, Expr checkExpr
where
  derefBeforeCheck(derefNode, derefExpr, checkNode, checkExpr, v, f) and
  // The variable should be a pointer.
  v.getType().getUnspecifiedType() instanceof PointerType
select derefExpr,
  "Pointer '" + v.getName() + "' is dereferenced here, but later checked for NULL at $@ in function '" + f.getName() + "'. Move the NULL check before the dereference.",
  checkExpr, "null check"
