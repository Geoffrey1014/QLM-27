/**
 * @name Unchecked regmap read return value
 * @description regmap_read/regmap_bulk_read/regmap_raw_read and related helpers can
 *              return a non-zero error code on failure (e.g. when the underlying bus
 *              transfer fails). Ignoring this error and using the data buffer can lead
 *              to acting on uninitialised or stale data. The result of these calls
 *              should be checked before the data they read is consumed.
 * @kind problem
 * @problem.severity warning
 * @id cpp/regmap-read-unchecked
 * @tags reliability
 *       correctness
 */

import cpp
import semmle.code.cpp.controlflow.Guards

/**
 * regmap read helpers that return an `int` error code and may fail. We deliberately
 * generalize beyond `regmap_bulk_read` (the API in the seed commit) to the whole
 * family of regmap read accessors.
 */
predicate isRegmapReadFunc(Function f) {
  exists(string n | n = f.getName() |
    n = "regmap_read" or
    n = "regmap_raw_read" or
    n = "regmap_bulk_read" or
    n = "regmap_noinc_read" or
    n = "regmap_multi_reg_read" or
    n = "regmap_fields_read" or
    n = "regmap_field_read"
  )
}

/** A call to a regmap read helper. */
class RegmapReadCall extends FunctionCall {
  RegmapReadCall() { isRegmapReadFunc(this.getTarget()) }
}

/**
 * Holds if the call's enclosing statement is an ExprStmt — i.e. the return value is
 * being discarded at the statement level. This is the classic "unchecked call" shape.
 */
predicate isDiscardedAsStatement(RegmapReadCall c) {
  exists(ExprStmt es | es.getExpr() = c)
}

/**
 * Holds if the return value of `c` is "used" in a way that constitutes an error check:
 * stored into a variable that is later inspected, used in a comparison, returned, or
 * otherwise consumed.
 */
predicate returnValueChecked(RegmapReadCall c) {
  // Direct expression-level uses: comparison, logical, not, cast-to-bool, etc.
  exists(Expr parent | parent = c.getParent() |
    parent instanceof ComparisonOperation or
    parent instanceof LogicalAndExpr or
    parent instanceof LogicalOrExpr or
    parent instanceof NotExpr or
    parent instanceof ConditionalExpr or
    parent instanceof AssignExpr
  )
  or
  // Wrapped in a cast which is itself checked / used.
  exists(Cast cast | cast = c.getParent() |
    cast.getParent() instanceof ComparisonOperation or
    cast.getParent() instanceof NotExpr or
    cast.getParent() instanceof LogicalAndExpr or
    cast.getParent() instanceof LogicalOrExpr or
    cast.getParent() instanceof ConditionalExpr or
    cast.getParent() instanceof AssignExpr or
    exists(ReturnStmt r | r.getExpr() = cast) or
    exists(IfStmt i | i.getCondition() = cast) or
    exists(WhileStmt w | w.getCondition() = cast) or
    exists(ForStmt f | f.getCondition() = cast) or
    exists(SwitchStmt s | s.getExpr() = cast)
  )
  or
  // Used directly as the condition of a control-flow construct.
  exists(IfStmt i | i.getCondition() = c)
  or
  exists(WhileStmt w | w.getCondition() = c)
  or
  exists(ForStmt f | f.getCondition() = c)
  or
  exists(DoStmt d | d.getCondition() = c)
  or
  exists(SwitchStmt s | s.getExpr() = c)
  or
  // Result is the return value of the enclosing function.
  exists(ReturnStmt r | r.getExpr() = c)
  or
  // Result assigned/initialized into a local, and that local is later examined.
  exists(LocalVariable v |
    v.getInitializer().getExpr() = c
    or
    exists(AssignExpr a | a.getRValue() = c and a.getLValue() = v.getAnAccess())
  |
    exists(VariableAccess va | va = v.getAnAccess() |
      va.getParent() instanceof ComparisonOperation or
      va.getParent() instanceof NotExpr or
      va.getParent() instanceof ReturnStmt or
      va.getParent() instanceof LogicalAndExpr or
      va.getParent() instanceof LogicalOrExpr or
      va.getParent() instanceof ConditionalExpr or
      exists(IfStmt i | i.getCondition() = va) or
      exists(WhileStmt w | w.getCondition() = va) or
      exists(ForStmt f | f.getCondition() = va) or
      exists(SwitchStmt s | s.getExpr() = va) or
      exists(FunctionCall fc | fc.getAnArgument() = va)
    )
  )
  or
  // Passed to another function (e.g. WARN_ON, dev_err, IS_ERR_VALUE, etc.).
  exists(FunctionCall fc | fc != c and fc.getAnArgument() = c)
}

/**
 * The data buffer argument (the one that gets filled in on success) of a regmap read
 * call. For the read helpers above this is typically argument index 1 or 2.
 */
Expr dataBufferArg(RegmapReadCall c) {
  result = c.getArgument(1) and
  c.getTarget().getName() in [
    "regmap_read", "regmap_field_read", "regmap_fields_read"
  ]
  or
  result = c.getArgument(2) and
  c.getTarget().getName() in [
    "regmap_raw_read", "regmap_bulk_read", "regmap_noinc_read"
  ]
}

from RegmapReadCall c
where
  // The return value is discarded at the statement level.
  isDiscardedAsStatement(c) and
  not returnValueChecked(c) and
  // Restrict to calls that actually have a buffer arg (so the missing check is
  // meaningful — the caller is going to consume data that may be invalid).
  exists(dataBufferArg(c))
select c,
  "Return value of " + c.getTarget().getName() +
    " is not checked; the read may have failed and the destination buffer may contain stale or uninitialised data."
