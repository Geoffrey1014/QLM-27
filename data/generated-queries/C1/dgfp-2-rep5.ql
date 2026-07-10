/**
 * @name mdelay() busy-wait in non-atomic context (should use msleep)
 * @description Detects calls to mdelay() with a delay long enough that a
 *              sleeping wait is preferable (>= 10 ms), occurring inside a
 *              function whose name suggests it runs in process/probe/init
 *              context rather than IRQ/atomic context. Such calls block the
 *              CPU unnecessarily and should be replaced with msleep() or
 *              usleep_range().
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-dgfp-2
 */

import cpp

/**
 * Holds if `f` is conservatively considered to run in atomic context, where
 * mdelay() (busy-wait) is the only legal choice. Name-based heuristic.
 */
predicate inAtomicLikeContext(Function f) {
  exists(string n | n = f.getName().toLowerCase() |
    n.matches("%_isr") or
    n.matches("%_irq%") or
    n.matches("%irq_handler%") or
    n.matches("%_handler") or
    n.matches("%_nmi%") or
    n.matches("%_tasklet%") or
    n.matches("%spin_%") or
    n.matches("%_atomic%") or
    n.matches("%softirq%")
  )
}

/**
 * Holds if `f` is conservatively considered to run in sleepable context,
 * based on common probe/init/resume/suspend/work naming.
 */
predicate inSleepableContext(Function f) {
  exists(string n | n = f.getName().toLowerCase() |
    n.matches("%_init") or
    n.matches("%_probe") or
    n.matches("%_resume%") or
    n.matches("%_suspend%") or
    n.matches("%_open") or
    n.matches("%_setup") or
    n.matches("%_start") or
    n.matches("%_work%") or
    n.matches("%_device_init%") or
    n.matches("%_thread%")
  )
}

from FunctionCall fc, Function callee, Function enclosing, int ms
where
  callee = fc.getTarget() and
  callee.getName() = "mdelay" and
  enclosing = fc.getEnclosingFunction() and
  // delay is a compile-time constant of at least 10 ms — long enough that
  // a sleep would be preferable.
  ms = fc.getArgument(0).getValue().toInt() and
  ms >= 10 and
  // exclude clearly-atomic enclosing functions; require a positive
  // sleepable-context signal OR absence of atomic-context signal.
  not inAtomicLikeContext(enclosing)
select fc,
  "mdelay(" + ms.toString() + ") busy-waits in '" + enclosing.getName() +
  "', which appears to run in non-atomic context; consider msleep()."
