/**
 * @name mdelay() used in sleepable context (delay-gfp pattern)
 * @description Detects calls to mdelay() (a busy-wait primitive) whose
 *              enclosing function runs in process / sleepable context
 *              (PM resume/suspend callback, probe, workqueue) where the
 *              sleeping equivalent msleep() should be used instead. Pattern
 *              derived from upstream commit e58650b57ee0 ("Input: wdt87xx_i2c
 *              - replace mdelay() with msleep() in wdt87xx_resume()"), one of
 *              the Bai/DCNS-style delay-gfp findings (ATC 2018 family).
 *
 *              The query gates on:
 *                P1. mdelay() with a non-trivial constant millisecond argument
 *                    (>= 10), filtering out short on-chip settling waits that
 *                    are typically expressed as udelay/mdelay(1).
 *                P2. enclosing function name matches a sleepable-context shape
 *                    (resume/suspend/probe/work).
 *                P3. enclosing function name does NOT match an atomic-context
 *                    shape (irq/handler/atomic/nmi/locked/tasklet), which is
 *                    where mdelay() is genuinely appropriate.
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3/c3/delay-gfp-mdelay-in-sleepable
 * @tags reliability
 *       delay-gfp
 *       performance
 */

import cpp

/* P1: mdelay() call with a constant millisecond argument >= 10. Short
 *     mdelay(1) / mdelay(0) idioms occur in genuinely atomic settle paths
 *     and are excluded by the threshold. */
predicate isBusyDelayCall(FunctionCall fc) {
  fc.getTarget().getName() = "mdelay" and
  exists(fc.getArgument(0).getValue().toInt()) and
  fc.getArgument(0).getValue().toInt() >= 10
}

/* P2: enclosing function looks like a sleepable-context entry point: PM
 *     resume/suspend callbacks, driver probe, workqueue handlers. */
predicate inSleepableContextByName(Function f) {
  exists(string n |
    n = f.getName() and
    (n.matches("%resume%") or
     n.matches("%suspend%") or
     n.matches("%probe%") or
     n.matches("%work%"))
  )
}

/* P3: enclosing function looks atomic — IRQ handler, NMI, holding a lock,
 *     tasklet/softirq context. Excluding these keeps the query silent on
 *     genuinely-correct mdelay() uses. */
predicate inAtomicContextByName(Function f) {
  exists(string n |
    n = f.getName() and
    (n.matches("%irq%") or
     n.matches("%handler%") or
     n.matches("%atomic%") or
     n.matches("%nmi%") or
     n.matches("%locked%") or
     n.matches("%tasklet%"))
  )
}

from FunctionCall fc, Function caller
where
  isBusyDelayCall(fc) and
  caller = fc.getEnclosingFunction() and
  inSleepableContextByName(caller) and
  not inAtomicContextByName(caller)
select fc,
       "mdelay(" + fc.getArgument(0).getValue() +
       ") in sleepable context (" + caller.getName() +
       "); should be msleep()"
