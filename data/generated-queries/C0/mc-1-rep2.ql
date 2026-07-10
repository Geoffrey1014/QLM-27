/**
 * @name Unchecked regmap read return value
 * @description regmap_read/regmap_bulk_read/regmap_raw_read and siblings can fail and
 *              return a non-zero error code. Ignoring that return value and consuming
 *              the (potentially uninitialised or stale) destination buffer is a bug,
 *              particularly inside interrupt handlers where bogus data leads to spurious
 *              wake-ups or scheduling.
 * @kind problem
 * @problem.severity warning
 * @id cpp/unchecked-regmap-read
 * @tags reliability
 *       correctness
 *       error-handling
 */

import cpp

/** A function in the regmap read family whose return value indicates success/failure. */
predicate isRegmapReadFn(Function f) {
  exists(string n | n = f.getName() |
    n = "regmap_read" or
    n = "regmap_bulk_read" or
    n = "regmap_raw_read" or
    n = "regmap_noinc_read" or
    n = "regmap_fields_read" or
    n = "regmap_multi_reg_read" or
    n = "regmap_bulk_read_async"
  )
}

/**
 * Holds if the call's return value is discarded - the call appears as an
 * ExprStmt (statement-expression) rather than being consumed by an
 * assignment, comparison, condition, return, or argument.
 */
predicate returnValueDiscarded(FunctionCall fc) {
  exists(ExprStmt es | es.getExpr() = fc)
}

from FunctionCall fc, Function callee
where
  fc.getTarget() = callee and
  isRegmapReadFn(callee) and
  returnValueDiscarded(fc) and
  // Exclude calls in test / sample harnesses where ignoring errors is intentional.
  not fc.getFile().getRelativePath().matches("%/tools/%") and
  not fc.getFile().getRelativePath().matches("%/samples/%")
select fc,
  "Return value of " + callee.getName() +
    "() is discarded; a failed read leaves the destination buffer with stale/uninitialised data."
