/**
 * @name Missing check of regmap_bulk_read return value (buffer used unchecked)
 * @description Detects calls to regmap_bulk_read whose return value is
 *              discarded (used as an expression-statement), leaving the
 *              caller to consume the read buffer without knowing whether
 *              the transfer actually succeeded. On failure the buffer
 *              contents are undefined and downstream logic (timers, event
 *              reports) may act on stale/garbage data.
 * @kind problem
 * @problem.severity warning
 * @id qlm/l0-mc1-regmap-bulk-read-unchecked
 */
import cpp

predicate isReadCall(FunctionCall fc) {
  fc.getTarget().getName() = "regmap_bulk_read"
}

from FunctionCall readCall, ExprStmt es
where isReadCall(readCall)
  and es.getExpr() = readCall
select readCall,
  "Return value of regmap_bulk_read is not checked in function '" +
  readCall.getEnclosingFunction().getName() +
  "' before consuming the read buffer; on failure the buffer contents are unreliable."
