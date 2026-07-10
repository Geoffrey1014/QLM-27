/**
 * @name  rq3-c2-mc-1-rep2
 * @id    cpp/rq3/c2/mc-1-rep2
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detect unchecked return values of regmap_bulk_read (and other
 *              fallible regmap_*_read variants) — a missing-check bug pattern.
 */

import cpp

/**
 * The call site invokes a regmap bulk/raw read API whose int return value
 * encodes a possible error (0 success, negative errno on failure).
 */
predicate isRegmapBulkReadCall(FunctionCall c) {
  exists(Function f | f = c.getTarget() |
    f.getName() = "regmap_bulk_read" or
    f.getName() = "regmap_raw_read" or
    f.getName() = "regmap_noinc_read" or
    f.getName() = "regmap_bulk_read_async"
  )
}

/**
 * The callee's return type is a signed integer that conventionally carries
 * an errno (this is true of all regmap_*_read APIs). Composed on top of the
 * recognizer above so we only flag calls whose semantics we understand.
 */
predicate returnsErrorCode(FunctionCall c) {
  isRegmapBulkReadCall(c) and
  c.getTarget().getType().getUnspecifiedType() instanceof IntType
}

/**
 * The return value is consumed (either by an assignment whose LHS is later
 * branched on, by a direct use in a control-flow condition, or by being
 * returned / passed to another check).
 */
predicate returnValueChecked(FunctionCall c) {
  returnsErrorCode(c) and
  (
    // Used directly inside an `if (...)` / `while (...)` / ternary condition.
    exists(ControlStructure cs | cs.getControllingExpr().getAChild*() = c)
    or
    // Stored into a variable that is later read inside a condition.
    exists(Variable v, AssignExpr a, ControlStructure cs |
      a.getRValue() = c and
      a.getLValue() = v.getAnAccess() and
      cs.getControllingExpr().getAChild*() = v.getAnAccess()
    )
    or
    // Declared with initializer = c, then tested.
    exists(LocalVariable v, ControlStructure cs |
      v.getInitializer().getExpr() = c and
      cs.getControllingExpr().getAChild*() = v.getAnAccess()
    )
    or
    // Returned directly from the enclosing function (caller will check).
    exists(ReturnStmt r | r.getExpr().getAChild*() = c)
    or
    // Passed to a check-style helper like IS_ERR / WARN_ON.
    exists(FunctionCall outer |
      outer.getAnArgument().getAChild*() = c and
      (outer.getTarget().getName().matches("IS_ERR%") or
       outer.getTarget().getName().matches("WARN%") or
       outer.getTarget().getName().matches("BUG%"))
    )
  )
}

/**
 * Top-level: the call returns an errno but its return value is never checked.
 */
predicate missingErrorCheck(FunctionCall c) {
  returnsErrorCode(c) and
  not returnValueChecked(c)
}

from FunctionCall c
where missingErrorCheck(c)
select c, "Missing check of return value from regmap_bulk_read (or similar fallible read)."
