/**
 * @name Pointer dereferenced before NULL check
 * @description A function-parameter pointer is dereferenced (or its address taken via
 *              field access) before being checked against NULL in the same function.
 *              If the caller can pass NULL, this causes a NULL pointer dereference.
 *              Mirrors bugs like rfkill_register's `&rfkill->dev` before `BUG_ON(!rfkill)`.
 * @kind problem
 * @problem.severity warning
 * @id cpp/deref-before-null-check
 * @tags reliability
 *       correctness
 *       security
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph

/**
 * A use of `p` that requires `p` to be non-NULL: either explicit pointer
 * dereference (`*p`), pointer arrow (`p->f`), array subscript (`p[i]`),
 * or being a qualifier on a field access whose address is taken (`&p->f`).
 */
class DerefUse extends Expr {
  Variable v;

  DerefUse() {
    exists(VariableAccess va | va = this.(PointerDereferenceExpr).getOperand() and va.getTarget() = v)
    or
    exists(PointerFieldAccess pfa, VariableAccess va |
      pfa = this and va = pfa.getQualifier() and va.getTarget() = v
    )
    or
    exists(ArrayExpr ae, VariableAccess va |
      ae = this and va = ae.getArrayBase() and va.getTarget() = v
    )
  }

  Variable getVariable() { result = v }
}

/**
 * A NULL check on `v` (either `!v`, `v == NULL`, `v == 0`, or symmetric).
 */
predicate isNullCheck(Expr e, Variable v) {
  exists(NotExpr n, VariableAccess va |
    n = e and va = n.getOperand() and va.getTarget() = v
  )
  or
  exists(EqualityOperation eq, VariableAccess va, Expr other |
    eq = e and
    (va = eq.getLeftOperand() and other = eq.getRightOperand()
     or
     va = eq.getRightOperand() and other = eq.getLeftOperand()) and
    va.getTarget() = v and
    (other instanceof NullValue or other.getValue() = "0")
  )
}

from Function f, Parameter p, DerefUse deref, Expr nullCheck
where
  p.getFunction() = f and
  p.getUnderlyingType() instanceof PointerType and
  deref.getVariable() = p and
  deref.getEnclosingFunction() = f and
  isNullCheck(nullCheck, p) and
  nullCheck.getEnclosingFunction() = f and
  // The dereference reaches the null check via control-flow (i.e. deref is
  // earlier in the CFG than the null check).
  deref.getASuccessor+() = nullCheck and
  // Exclude cases where there's a prior null check that already guards the deref.
  not exists(Expr priorCheck |
    isNullCheck(priorCheck, p) and
    priorCheck.getEnclosingFunction() = f and
    priorCheck.getASuccessor+() = deref
  )
select deref,
  "Pointer parameter '$@' is dereferenced here before being checked for NULL at $@.",
  p, p.getName(), nullCheck, "this later check"
