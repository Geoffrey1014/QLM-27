/**
 * @name  rq3-c2-mc-1-rep4
 * @id    cpp/rq3/c2/mc-1-rep4
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects unchecked return values from regmap_bulk_read().
 */
import cpp

/**
 * Predicate 1: identifies calls to regmap_bulk_read.
 */
predicate isRegmapBulkReadCall(FunctionCall fc) {
  fc.getTarget().getName() = "regmap_bulk_read"
}

/**
 * Predicate 2: the return value of the call is discarded — call appears
 * as an expression statement on its own.
 */
predicate returnValueDiscarded(FunctionCall fc) {
  exists(ExprStmt es | es.getExpr() = fc)
}

/**
 * Predicate 3: the call is not part of an if-condition and isn't compared.
 */
predicate notUsedInCondition(FunctionCall fc) {
  not exists(IfStmt ifs | ifs.getCondition().getAChild*() = fc) and
  not exists(ComparisonOperation co | co.getAnOperand().getAChild*() = fc)
}

/**
 * Predicate 4: assembled pattern — unchecked regmap_bulk_read call.
 */
predicate uncheckedRegmapBulkRead(FunctionCall fc) {
  isRegmapBulkReadCall(fc) and
  returnValueDiscarded(fc) and
  notUsedInCondition(fc)
}

from FunctionCall fc
where uncheckedRegmapBulkRead(fc)
select fc, "Return value of regmap_bulk_read() is not checked for error."
