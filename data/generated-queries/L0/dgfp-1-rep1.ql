/**
 * @name mdelay() used in sleepable context (delay-gfp pattern) [L0]
 * @description Detects mdelay() calls (busy-wait) whose enclosing function
 *              looks like a sleepable-context entry point (resume/suspend/
 *              probe/work) and does NOT look like an atomic-context entry
 *              point (irq/handler/atomic/nmi/locked/tasklet). Pattern from
 *              commit e58650b57ee0 ("Input: wdt87xx_i2c - replace mdelay()
 *              with msleep() in wdt87xx_resume()").
 *
 *              L0 zero-shot variant: only one helper predicate is defined
 *              (busy-delay call recognition); the sleepable/atomic
 *              context tests are inlined in the assembly where-clause.
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3/l0/delay-gfp-mdelay-in-sleepable
 * @tags reliability
 *       delay-gfp
 *       performance
 */

import cpp

predicate isBusyDelayCall(FunctionCall fc) {
  fc.getTarget().getName() = "mdelay" and
  exists(fc.getArgument(0).getValue().toInt()) and
  fc.getArgument(0).getValue().toInt() >= 10
}

from FunctionCall fc, Function caller
where
  isBusyDelayCall(fc) and
  caller = fc.getEnclosingFunction() and
  (caller.getName().matches("%resume%") or
   caller.getName().matches("%suspend%") or
   caller.getName().matches("%probe%") or
   caller.getName().matches("%work%")) and
  not (caller.getName().matches("%irq%") or
       caller.getName().matches("%handler%") or
       caller.getName().matches("%atomic%") or
       caller.getName().matches("%nmi%") or
       caller.getName().matches("%locked%") or
       caller.getName().matches("%tasklet%"))
select fc,
       "mdelay(" + fc.getArgument(0).getValue() +
       ") in sleepable context (" + caller.getName() +
       "); should be msleep()"
