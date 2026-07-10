/**
 * @name Missing check of regmap read return value in IRQ-like handler
 * @description Detects calls to read-style regmap APIs whose return value is
 *              silently dropped (expression-statement context or (void)-cast)
 *              while a downstream call in the same function proceeds to
 *              consume the buffer the read populated. Pattern derived from
 *              upstream commit e85bb0beb649 ("Input: ad7879 - add check for
 *              read errors in interrupt").
 * @kind problem
 * @problem.severity warning
 * @id qlm/l1-mc1-missing-check-regmap-read
 * @tags reliability
 *       missing-check
 */

import cpp

predicate isReadApi(FunctionCall fc) {
  fc.getTarget().getName() = "regmap_bulk_read" or
  fc.getTarget().getName() = "regmap_read" or
  fc.getTarget().getName() = "regmap_raw_read"
}

predicate isResultDiscarded(FunctionCall fc) {
  fc instanceof ExprInVoidContext
  or
  exists(CStyleCast c | c.getExpr() = fc and c.getType() instanceof VoidType)
}

from FunctionCall fc, Function enclosing
where isReadApi(fc)
  and isResultDiscarded(fc)
  and enclosing = fc.getEnclosingFunction()
  and exists(FunctionCall later |
    later.getEnclosingFunction() = enclosing and
    later.getLocation().getStartLine() > fc.getLocation().getStartLine()
  )
select fc, "Unchecked read-API result in " + enclosing.getName()
