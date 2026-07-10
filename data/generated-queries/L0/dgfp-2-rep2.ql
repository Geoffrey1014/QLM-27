/**
 * @name mdelay in likely sleepable context
 * @description Detects mdelay() calls with a delay of at least 10ms whose
 *              enclosing function is not obviously an IRQ / tasklet / ISR
 *              handler. In sleepable contexts msleep() should be used
 *              instead of busy-waiting.
 * @kind problem
 * @problem.severity warning
 * @id cpp/dgfp-2-rep2-l0
 */

import cpp

predicate isMdelayCall(FunctionCall fc) {
  fc.getTarget().getName() = "mdelay" and
  exists(Expr arg | arg = fc.getArgument(0) | arg.getValue().toInt() >= 10)
}

from FunctionCall fc, Function enclosing
where
  isMdelayCall(fc) and
  enclosing = fc.getEnclosingFunction() and
  not enclosing.getName().matches("%irq%") and
  not enclosing.getName().matches("%handler%") and
  not enclosing.getName().matches("%tasklet%") and
  not enclosing.getName().matches("%isr%")
select fc,
  "mdelay() called in likely sleepable context (enclosing function: " +
    enclosing.getName() + ") - consider msleep()"
