/**
 * @name Pointer dereferenced before NULL check
 * @description A pointer-typed parameter (or local) is dereferenced before being
 *              checked for NULL in the same function. The NULL check is therefore
 *              dead/unreachable in the !=NULL sense, and if the pointer ever is
 *              NULL the dereference crashes the kernel. Pattern derived from the
 *              rfkill_register fix (commit 6fc232db9e8c) where `&rfkill->dev`
 *              was taken before `BUG_ON(!rfkill)`.
 * @kind problem
 * @problem.severity error
 * @id cpp/kernel-deref-before-null-check
 * @tags reliability
 *       security
 *       correctness
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph

/**
 * Holds if `e` is an expression that dereferences pointer variable `v`
 * (either `*v`, `v->field`, or `&v->field` which still requires `v` non-null).
 */
predicate derefOfVar(Expr e, Variable v) {
  exists(PointerDereferenceExpr pde |
    pde = e and
    pde.getOperand() = v.getAnAccess()
  )
  or
  exists(PointerFieldAccess pfa |
    pfa = e and
    pfa.getQualifier() = v.getAnAccess()
  )
  or
  // taking address of a subfield via -> also requires the base pointer to be non-null
  exists(AddressOfExpr aoe, PointerFieldAccess pfa |
    aoe = e and
    aoe.getOperand() = pfa and
    pfa.getQualifier() = v.getAnAccess()
  )
}

/**
 * Holds if `e` is a NULL-check on variable `v`. We accept:
 *   - `!v`
 *   - `v == NULL` / `NULL == v`
 *   - `v != NULL` / `NULL != v`
 *   - `BUG_ON(!v)` / `WARN_ON(!v)` / `if (!v) return ...`
 * We are interested in the location of the check, not its polarity.
 */
predicate nullCheckOfVar(Expr e, Variable v) {
  exists(NotExpr ne |
    ne = e and
    ne.getOperand() = v.getAnAccess()
  )
  or
  exists(EqualityOperation eq |
    eq = e and
    eq.getAnOperand() = v.getAnAccess() and
    eq.getAnOperand().getValue() = "0"
  )
}

/**
 * Holds if variable `v` is a pointer-typed local/parameter in function `f`
 * whose value originates outside the function (parameter, or the result of
 * an external/extern-like call we don't model).  We restrict to parameters
 * to keep false positives bounded.
 */
predicate ptrParam(Function f, Parameter v) {
  v.getFunction() = f and
  v.getType().getUnspecifiedType() instanceof PointerType
}

/**
 * Holds if dereference `d` precedes null-check `c` in the control-flow graph
 * of function `f`, and both reference parameter `v`.
 */
predicate derefBeforeNullCheck(Function f, Parameter v, Expr d, Expr c) {
  ptrParam(f, v) and
  d.getEnclosingFunction() = f and
  c.getEnclosingFunction() = f and
  derefOfVar(d, v) and
  nullCheckOfVar(c, v) and
  // structural ordering: d's control-flow node strictly precedes c's
  exists(ControlFlowNode dn, ControlFlowNode cn |
    dn = d and
    cn = c and
    dn.getASuccessor+() = cn
  ) and
  // Exclude the case where the deref is itself dominated by an earlier null
  // check of the same variable.
  not exists(Expr earlier |
    nullCheckOfVar(earlier, v) and
    earlier.getEnclosingFunction() = f and
    exists(ControlFlowNode en, ControlFlowNode dn2 |
      en = earlier and dn2 = d and en.getASuccessor+() = dn2
    )
  )
}

from Function f, Parameter v, Expr d, Expr c
where
  derefBeforeNullCheck(f, v, d, c) and
  // keep one (deref, check) pair per (function, variable) to avoid duplicate alerts
  d = min(Expr d0 |
        derefBeforeNullCheck(f, v, d0, _) |
        d0 order by d0.getLocation().getStartLine(), d0.getLocation().getStartColumn()
      ) and
  c = min(Expr c0 |
        derefBeforeNullCheck(f, v, _, c0) |
        c0 order by c0.getLocation().getStartLine(), c0.getLocation().getStartColumn()
      )
select d,
  "Pointer parameter '$@' is dereferenced here before being checked for NULL at $@ in function '"
    + f.getName() + "'.",
  v, v.getName(), c, c.toString()
