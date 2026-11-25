/**
 * @name ERR_PTR / IS_ERR confusion (error-pointer dereference)
 * @description A function returns ERR_PTR()/ERR_CAST() (an error-valued pointer like
 *              (void*)-EINVAL) on failure. A caller stores the result and then dereferences
 *              it on a path that is NOT dominated by an IS_ERR()/IS_ERR_OR_NULL()/PTR_ERR()
 *              guard on that same value. Shape (A) WRONG-GUARD: the caller guards with
 *              `if (!p)` / `if (p == NULL)` instead of IS_ERR(p) -- an error pointer slips
 *              through and is dereferenced (textbook one-line Fixes:/stable bug). Shape (B)
 *              UNCHECKED: no IS_ERR/NULL guard dominates the dereference at all.
 *
 *              Precision relies on (1) SSA reaching definitions -- the dereferenced use must
 *              be defined *directly* by the producer call with no intervening reassignment or
 *              phi-merge (this kills the "IS_ERR check then reassign on the error branch" and
 *              "deref actually uses a different producer's value" false positives), and (2)
 *              real guard dominance (semmle IRGuards GuardCondition), NOT textual proximity,
 *              because IS_ERR frequently sits one line below an of_node_put() cleanup and
 *              naive proximity massively over-flags.
 * @kind problem
 * @problem.severity warning
 * @precision medium
 * @id cpp/err-ptr-confusion
 * @tags security
 *       reliability
 */

import cpp
import semmle.code.cpp.controlflow.Guards
import semmle.code.cpp.controlflow.SSA

/* ------------------------------------------------------------------ *
 *  Producers: functions that can return an error pointer.
 * ------------------------------------------------------------------ */

/** A call to the ERR_PTR / ERR_CAST / IOMEM_ERR_PTR error-pointer-creating helpers. */
predicate isErrPtrMakingCall(FunctionCall fc) {
  fc.getTarget().getName() in ["ERR_PTR", "ERR_CAST", "ERR_PTR_PCPU", "IOMEM_ERR_PTR"]
}

/**
 * A "producer" function: some return statement in it returns an expression whose
 * subtree contains an ERR_PTR/ERR_CAST call. This is the enumerable, taint-free anchor.
 */
class ErrPtrProducer extends Function {
  ErrPtrProducer() {
    exists(ReturnStmt ret | ret.getEnclosingFunction() = this |
      isErrPtrMakingCall(ret.getExpr().getAChild*())
    )
  }
}

/* ------------------------------------------------------------------ *
 *  Dereferences of a variable access.
 * ------------------------------------------------------------------ */

/**
 * Holds if `deref` is an expression that dereferences variable access `va`:
 *   p->x (field access / indirect call through field), p[i], *p.
 */
predicate isDerefOf(Expr deref, VariableAccess va) {
  // p->field  (field access on a pointer)
  deref.(FieldAccess).getQualifier() = va and
  va.getType().getUnspecifiedType() instanceof PointerType
  or
  // p[i]
  deref.(ArrayExpr).getArrayBase() = va
  or
  // *p
  deref.(PointerDereferenceExpr).getOperand() = va
}

/* ------------------------------------------------------------------ *
 *  Guards on a value.
 * ------------------------------------------------------------------ */

/** A guard whose condition tests the result of IS_ERR / IS_ERR_OR_NULL / PTR_ERR on `v`. */
predicate isErrGuardOn(GuardCondition g, StackVariable v) {
  exists(FunctionCall chk |
    chk.getTarget().getName() in [
        "IS_ERR", "IS_ERR_OR_NULL", "PTR_ERR", "IS_ERR_PCPU", "PTR_ERR_PCPU",
        "IS_ERR_VALUE", "PTR_ERR_OR_ZERO"
      ] and
    chk.getAnArgument().getAChild*().(VariableAccess).getTarget() = v and
    (chk = g.(Expr) or chk = g.(Expr).getAChild*())
  )
}

/** A NULL-style guard on `v`: `v == NULL`, `v != NULL`, `!v`, or bare `if (v)`. */
predicate isNullGuardOn(GuardCondition g, StackVariable v) {
  // v == NULL / v != NULL / NULL == v ...
  exists(EqualityOperation eq | eq = g.(Expr) or eq = g.(Expr).getAChild*() |
    eq.getAnOperand().(VariableAccess).getTarget() = v and
    eq.getAnOperand().getValue() = "0"
  )
  or
  // !v
  exists(NotExpr ne | ne = g.(Expr) or ne = g.(Expr).getAChild*() |
    ne.getOperand().(VariableAccess).getTarget() = v
  )
  or
  // bare `if (v)` where the guard *is* the variable access itself
  g.(Expr).(VariableAccess).getTarget() = v
}

/* ------------------------------------------------------------------ *
 *  Dominance helpers (real guard dominance, not textual proximity).
 * ------------------------------------------------------------------ */

/** Holds if some IS_ERR-style guard on `v` controls (dominates) the basic block of `use`. */
predicate isErrDominates(Expr use, StackVariable v) {
  exists(GuardCondition g | isErrGuardOn(g, v) and g.controls(use.getBasicBlock(), _))
}

/** Holds if some NULL-style guard on `v` controls (dominates) the basic block of `use`. */
predicate nullDominates(Expr use, StackVariable v) {
  exists(GuardCondition g | isNullGuardOn(g, v) and g.controls(use.getBasicBlock(), _))
}

/* ------------------------------------------------------------------ *
 *  Noise exclusions (reuse the project's conventions).
 * ------------------------------------------------------------------ */

predicate inExcludedFile(Element e) {
  e.getFile().getRelativePath().regexpMatch("(?i).*(/test|_test|/kunit|/selftest|/tests/).*")
  or
  e.getFile().getRelativePath().regexpMatch("^(scripts|tools|samples|Documentation)/.*")
}

/* ------------------------------------------------------------------ *
 *  Core relation: a producer value dereffed via SSA reaching def.
 * ------------------------------------------------------------------ */

/**
 * Holds if `va` is a use of `v` whose SSA reaching definition is *directly* (no phi merge,
 * no intervening reassignment) the producer call `fc`, and `va` is dereferenced by `deref`.
 * `prod` is the producer function called at `fc`.
 */
predicate errPtrDeref(
  StackVariable v, ErrPtrProducer prod, FunctionCall fc, VariableAccess va, Expr deref
) {
  fc.getTarget() = prod and
  prod != fc.getEnclosingFunction() and
  exists(SsaDefinition def |
    va = def.getAUse(v) and
    def.getDefiningValue(v) = fc
  ) and
  isDerefOf(deref, va)
}

/**
 * The classification of an offending dereference.
 *   "A" = wrong-guard (NULL-guarded but not IS_ERR-guarded)
 *   "B" = unchecked   (neither IS_ERR- nor NULL-guarded)
 */
string shapeOf(Expr use, StackVariable v) {
  not isErrDominates(use, v) and nullDominates(use, v) and result = "A"
  or
  not isErrDominates(use, v) and not nullDominates(use, v) and result = "B"
}

/** Human-readable guard description for the message. */
string guardDesc(string shape) {
  shape = "A" and result = "guarded only by a NULL check (wrong guard)"
  or
  shape = "B" and result = "with no IS_ERR/NULL guard"
}

from
  StackVariable v, ErrPtrProducer prod, FunctionCall fc, VariableAccess va, Expr deref, string shape,
  Function caller
where
  errPtrDeref(v, prod, fc, va, deref) and
  caller = deref.getEnclosingFunction() and
  shape = shapeOf(va, v) and
  not inExcludedFile(deref) and
  // Keep one row per (caller, variable, deref-line): the earliest offending deref.
  deref.getLocation().getStartLine() =
    min(VariableAccess va2, Expr d2 |
      errPtrDeref(v, prod, _, va2, d2) and
      d2.getEnclosingFunction() = caller and
      exists(shapeOf(va2, v))
    |
      d2.getLocation().getStartLine()
    )
select deref,
  "[" + shape + "] " + deref.getLocation().getFile().getRelativePath() + ":" +
    deref.getLocation().getStartLine().toString() + " error pointer from '" + prod.getName() +
    "()' (call L" + fc.getLocation().getStartLine().toString() + ") dereferenced via '" +
    v.getName() + "' " + guardDesc(shape)
