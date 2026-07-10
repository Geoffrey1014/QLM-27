/**
 * @name Pointer dereferenced before NULL check
 * @description A pointer is dereferenced (via field access, array indexing, or
 *              passed as an implicit receiver to an inline accessor) and then
 *              later compared against NULL on a reachable path. Either the
 *              earlier dereference is unsafe, or the later NULL check is dead
 *              code. Typical kernel example: taking the address of a member
 *              (`&p->dev`) before validating `p`.
 * @kind problem
 * @problem.severity warning
 * @id cpp/deref-before-null-check
 * @tags reliability
 *       security
 *       correctness
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph

/**
 * An expression that dereferences `p` in a way that crashes if `p` is NULL.
 * Covers:
 *   - `*p`
 *   - `p->field`
 *   - `&p->field`             (address-of-member on a NULL pointer faults
 *                              for any non-zero member offset, and is the
 *                              exact shape of the rfkill_register bug:
 *                              `struct device *dev = &rfkill->dev;` before
 *                              checking `rfkill`.)
 *   - `p[i]`
 */
predicate dereferences(Expr deref, Variable v) {
  exists(VariableAccess va | va = v.getAnAccess() |
    // *v   or   v->field   (PointerFieldAccess covers `->`)
    deref.(PointerDereferenceExpr).getOperand() = va
    or
    deref.(PointerFieldAccess).getQualifier() = va
    or
    // &v->field  -- address-of a field reached through v
    exists(PointerFieldAccess pfa |
      pfa.getQualifier() = va and
      deref.(AddressOfExpr).getOperand() = pfa
    )
    or
    // v[i]
    deref.(ArrayExpr).getArrayBase() = va
  )
}

/**
 * `cmp` is a comparison of `v` against a null constant (or its negation in a
 * condition, e.g. `if (!v)`).
 */
predicate isNullCheck(Expr cmp, Variable v) {
  exists(VariableAccess va | va = v.getAnAccess() |
    // v == NULL / v != NULL / NULL == v / NULL != v
    exists(EqualityOperation eq |
      eq = cmp and
      eq.getAnOperand() = va and
      eq.getAnOperand().getValue() = "0"
    )
    or
    // !v  used as a condition
    exists(NotExpr ne |
      ne = cmp and
      ne.getOperand() = va
    )
    or
    // bare `if (v)` -- v itself used as a guard
    exists(ControlFlowNode guard |
      guard = va and
      (
        exists(IfStmt is | is.getCondition() = va) or
        exists(ConditionalExpr ce | ce.getCondition() = va)
      ) and
      cmp = va
    )
  )
}

/**
 * `deref` (which dereferences `v`) is followed on the CFG by a NULL check
 * `cmp` on the same variable, in the same function, with no intervening
 * assignment to `v`.
 */
predicate derefThenNullCheck(Expr deref, Expr cmp, Variable v, Function f) {
  dereferences(deref, v) and
  isNullCheck(cmp, v) and
  deref.getEnclosingFunction() = f and
  cmp.getEnclosingFunction() = f and
  deref.getLocation().getStartLine() < cmp.getLocation().getStartLine() and
  // Reachability: cmp is a CFG successor of deref.
  deref.(ControlFlowNode).getASuccessor*() = cmp and
  // No reassignment of v between the deref and the check that would make the
  // later check meaningful (a new value justifies a new null test).
  not exists(Assignment asn |
    asn.getLValue() = v.getAnAccess() and
    asn.getEnclosingFunction() = f and
    asn.getLocation().getStartLine() > deref.getLocation().getStartLine() and
    asn.getLocation().getStartLine() < cmp.getLocation().getStartLine()
  )
}

from Expr deref, Expr cmp, Variable v, Function f
where
  // Only flag parameters or locals that could plausibly be NULL on entry.
  (v instanceof Parameter or v instanceof LocalVariable) and
  v.getType().getUnspecifiedType() instanceof PointerType and
  derefThenNullCheck(deref, cmp, v, f) and
  // Same translation unit / file: avoid noise from macro-expanded headers.
  deref.getFile() = cmp.getFile()
select deref,
  "Pointer '" + v.getName() + "' is dereferenced here but later checked for NULL at $@ in function '"
    + f.getName() + "'.", cmp, "this null check"
