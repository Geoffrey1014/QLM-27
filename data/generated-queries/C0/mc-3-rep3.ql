/**
 * @name Pointer dereferenced before NULL check
 * @description A pointer parameter is dereferenced before it is checked against NULL
 *              in the same function. Either the NULL check is dead code, or the prior
 *              dereference is a bug that can lead to a NULL pointer dereference.
 *              Modeled after the rfkill_register fix (commit 6fc232db9e8c) which moved
 *              the !rfkill check before the &rfkill->dev dereference.
 * @kind problem
 * @problem.severity warning
 * @id cpp/deref-before-null-check-param
 * @tags reliability
 *       correctness
 *       security
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph

/**
 * A NULL check on a pointer variable, e.g. `if (!p)`, `if (p == NULL)`,
 * `if (p != NULL)`, `BUG_ON(!p)`, `WARN_ON(!p)`, etc.
 */
predicate isNullCheckOf(Expr check, Variable v) {
  exists(VariableAccess va | va = v.getAnAccess() |
    // !p   or   p
    check = va and check.getFullyConverted().getType() instanceof BoolType
    or
    // p == NULL / p != NULL / NULL == p / NULL != p
    exists(EqualityOperation eq |
      eq = check and
      eq.getAnOperand() = va and
      eq.getAnOperand().getValue() = "0"
    )
    or
    // !p
    exists(NotExpr ne | ne = check and ne.getOperand() = va)
    or
    // !p inside a wrapper expression
    exists(NotExpr ne |
      ne.getOperand() = va and
      check.getAChild*() = ne
    )
  )
}

/**
 * Holds if `e` is a dereference of variable `v` (either `*v`, `v->x`, or `v[i]`).
 */
predicate isDerefOf(Expr e, Variable v) {
  exists(VariableAccess va | va = v.getAnAccess() |
    // *v
    exists(PointerDereferenceExpr pde | pde = e and pde.getOperand() = va)
    or
    // v->field
    exists(PointerFieldAccess pfa | pfa = e and pfa.getQualifier() = va)
    or
    // v[i]
    exists(ArrayExpr ae | ae = e and ae.getArrayBase() = va)
    or
    // &v->field — taking address still dereferences v
    exists(PointerFieldAccess pfa |
      pfa.getQualifier() = va and
      e.(AddressOfExpr).getOperand() = pfa
    )
  )
}

/**
 * Holds if `check` is a NULL-check on `v` reachable from control-flow
 * predecessor `deref`.
 */
predicate derefThenCheck(Expr deref, Expr check, Variable v, Function f) {
  isDerefOf(deref, v) and
  isNullCheckOf(check, v) and
  deref.getEnclosingFunction() = f and
  check.getEnclosingFunction() = f and
  deref != check and
  // control-flow: deref strictly before check
  deref.getASuccessor+() = check
}

/**
 * Restrict to function parameters: these are the cases where the caller may
 * legitimately pass NULL and the dereference is a real bug.
 */
from Function f, Parameter p, Expr deref, Expr check
where
  p.getFunction() = f and
  p.getType() instanceof PointerType and
  derefThenCheck(deref, check, p, f) and
  // Avoid macro-expansion noise: require the dereference to come from real source.
  not deref.isInMacroExpansion() and
  // Heuristic: only flag if the NULL-check appears to be a guard (has an early exit
  // or BUG-style macro) — otherwise the check might just be defensive after a
  // known-non-null deref. We approximate by requiring the check to be in an
  // IfStmt condition.
  exists(IfStmt is | is.getCondition().getAChild*() = check or is.getCondition() = check)
select deref,
  "Pointer parameter '" + p.getName() + "' is dereferenced here before being checked for NULL at $@.",
  check, "this NULL check"
