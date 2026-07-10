/**
 * @name Unchecked regmap read return value
 * @description The return value of regmap_read / regmap_bulk_read / regmap_raw_read
 *              and friends indicates whether the I/O succeeded. Ignoring it can
 *              cause downstream logic (timers, decisions, reports) to act on
 *              uninitialized or stale data. This query flags calls whose return
 *              value is neither assigned, checked, nor otherwise used.
 * @kind problem
 * @problem.severity warning
 * @id cpp/unchecked-regmap-read
 * @tags reliability
 *       correctness
 *       error-handling
 */

import cpp

/**
 * A function in the regmap read family. We match by name so that the pattern
 * generalizes to all regmap_*_read variants (bulk, raw, noinc, etc.) without
 * hard-coding a single API.
 */
class RegmapReadFunction extends Function {
  RegmapReadFunction() {
    exists(string n | n = this.getName() |
      n = "regmap_read" or
      n = "regmap_bulk_read" or
      n = "regmap_raw_read" or
      n = "regmap_noinc_read" or
      n = "regmap_multi_reg_read" or
      n = "regmap_fields_read" or
      n = "regmap_field_read" or
      n = "regmap_read_poll_timeout" or
      n = "regmap_bulk_read_async"
    )
  }
}

/**
 * Holds if `call` has its return value used in some way — assigned to a
 * variable, compared, returned, passed as an argument, or otherwise consumed.
 * A call whose result is discarded (appears as an expression-statement) will
 * NOT satisfy this predicate.
 */
predicate returnValueUsed(FunctionCall call) {
  // The call is not the top-level expression of an ExprStmt — i.e., its
  // value flows somewhere. Equivalently: its parent is not an ExprStmt.
  not call.getParent() instanceof ExprStmt
}

/**
 * Holds if `call` sits inside a conditional construct that immediately tests
 * a sibling variable assigned from this call. We use the structural check
 * above (`returnValueUsed`) as the primary signal; this is reserved for
 * future refinement.
 */
predicate inErrorHandlingContext(FunctionCall call) {
  exists(IfStmt ifs | ifs.getCondition() = call)
  or
  exists(IfStmt ifs |
    ifs.getCondition().getAChild*() = call
  )
}

from FunctionCall call, RegmapReadFunction f
where
  call.getTarget() = f and
  // Result is discarded: appears as the whole expression of an ExprStmt.
  not returnValueUsed(call) and
  // Defensive: exclude any case where the call still ended up wired into a
  // conditional (shouldn't happen given the above, but guards against
  // unusual AST shapes such as comma operators).
  not inErrorHandlingContext(call)
select call,
  "Return value of " + f.getName() +
    "() is ignored; the call can fail and downstream logic may act on stale data."
