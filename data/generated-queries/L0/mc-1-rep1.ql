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
 * @id qlm/l0-mc1-missing-check-regmap-read
 * @tags reliability
 *       missing-check
 */

import cpp

predicate isReadApi(FunctionCall fc) {
  fc.getTarget().getName() = "regmap_bulk_read" or
  fc.getTarget().getName() = "regmap_read"
}

from FunctionCall fc, Function enclosing
where isReadApi(fc)
  and enclosing = fc.getEnclosingFunction()
  and (
    fc instanceof ExprInVoidContext or
    exists(CStyleCast c | c.getExpr() = fc and c.getType() instanceof VoidType)
  )
  and exists(FunctionCall later |
    later.getEnclosingFunction() = enclosing and
    later.getLocation().getStartLine() > fc.getLocation().getStartLine() and
    (later.getTarget().getName() = "ad7879_report" or
     later.getTarget().getName() = "mod_timer")
  )
select fc, "Unchecked read-API result; buffer is consumed downstream (missing-check) in " + enclosing.getName()
