/**
 * @name Missing return-value check after regmap_bulk_read
 * @description Detects call sites of fallible read APIs whose return value
 *              is discarded, mirroring the pattern fixed in commit
 *              e85bb0beb649 (Input: ad7879 - add check for read errors in
 *              interrupt).
 * @kind problem
 * @problem.severity warning
 * @id qlm/missing-check-regmap-bulk-read
 */

import cpp

predicate isFallibleReadCall(FunctionCall fc) {
  fc.getTarget().getName() = "regmap_bulk_read"
}

predicate isReturnValueDiscarded(FunctionCall fc) {
  exists(ExprStmt es | es.getExpr() = fc)
}

from FunctionCall fc
where isFallibleReadCall(fc) and isReturnValueDiscarded(fc)
select fc,
  "return value of " + fc.getTarget().getName() +
  " is discarded; caller cannot detect I/O failure"
