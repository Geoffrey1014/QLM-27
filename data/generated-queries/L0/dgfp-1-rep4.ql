/**
 * @name mdelay() used in sleepable context (delay-gfp, L0 zero-shot)
 * @description Detects mdelay() calls whose enclosing function name matches
 *              a sleepable-context shape (resume/suspend/probe/work) and does
 *              NOT match an atomic-context shape (irq/handler/atomic/nmi/
 *              locked/tasklet). Pattern derived from upstream commit
 *              e58650b57ee0 (wdt87xx_i2c mdelay -> msleep). L0 zero-shot
 *              rendering: a single structural predicate + a from-where-select.
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3/l0/delay-gfp-mdelay-in-sleepable-dgfp1-rep4
 * @tags reliability
 *       delay-gfp
 *       performance
 */

import cpp

predicate isMdelayInSleepableCaller(FunctionCall fc) {
  fc.getTarget().getName() = "mdelay" and
  exists(Function f |
    f = fc.getEnclosingFunction() and
    (f.getName().matches("%resume%") or
     f.getName().matches("%suspend%") or
     f.getName().matches("%probe%") or
     f.getName().matches("%work%")) and
    not (f.getName().matches("%irq%") or
         f.getName().matches("%handler%") or
         f.getName().matches("%atomic%") or
         f.getName().matches("%nmi%") or
         f.getName().matches("%locked%") or
         f.getName().matches("%tasklet%"))
  )
}

from FunctionCall fc, Function caller
where
  isMdelayInSleepableCaller(fc) and
  caller = fc.getEnclosingFunction()
select fc,
  "mdelay() in sleepable context '" + caller.getName() +
  "' — should be msleep()"
