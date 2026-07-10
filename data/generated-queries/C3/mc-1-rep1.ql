/**
 * @name Missing check of regmap_bulk_read return value in IRQ-like handler
 * @description Detects calls to read-style regmap APIs whose return value is
 *              silently dropped (expression-statement context or (void)-cast)
 *              while a downstream consumer in the same function uses the
 *              buffer the call filled. Pattern derived from upstream commit
 *              e85bb0beb649 ("Input: ad7879 - add check for read errors in
 *              interrupt").
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3/c3/missing-check-regmap-read
 * @tags reliability
 *       missing-check
 */

import cpp

/* P1: target read-style regmap APIs whose return signals success/failure. */
predicate isReadApi(FunctionCall fc) {
  fc.getTarget().getName() = "regmap_bulk_read" or
  fc.getTarget().getName() = "regmap_read"
}

/* P2: return value silently dropped — call appears as a standalone
 *     expression-statement, or is wrapped in an explicit (void) cast. */
predicate returnValueDropped(FunctionCall fc) {
  fc instanceof ExprInVoidContext or
  exists(CStyleCast c | c.getExpr() = fc and c.getType() instanceof VoidType)
}

/* P3: a later call in the same enclosing function consumes data that
 *     depends on the read having succeeded (proxy: ad7879_report /
 *     mod_timer downstream — extend list for other drivers as needed). */
predicate downstreamConsumesBuffer(FunctionCall fc) {
  exists(FunctionCall later, Function enclosing |
    enclosing = fc.getEnclosingFunction() and
    later.getEnclosingFunction() = enclosing and
    later.getLocation().getStartLine() > fc.getLocation().getStartLine() and
    (later.getTarget().getName() = "ad7879_report" or
     later.getTarget().getName() = "mod_timer"))
}

from FunctionCall fc
where isReadApi(fc) and
      returnValueDropped(fc) and
      downstreamConsumesBuffer(fc)
select fc,
       "Unchecked read-API result; buffer is consumed downstream " +
       "(missing-check) in " + fc.getEnclosingFunction().getName()
