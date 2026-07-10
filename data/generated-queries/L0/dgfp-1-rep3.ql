/**
 * @name mdelay() in sleepable context (replace with msleep)
 * @description Flags calls to mdelay() that occur inside a function whose
 *              name strongly indicates a sleepable context (PM resume /
 *              suspend / probe / init / open / release / remove callback),
 *              and not inside a name-recognised atomic / IRQ handler.
 *              Such calls busy-wait the CPU pointlessly; msleep() or
 *              usleep_range() should be used instead.
 * @kind problem
 * @problem.severity warning
 * @id qlm/l0-dgfp1-mdelay-in-sleepable
 * @tags reliability
 *       performance
 *       linux-kernel
 */

import cpp

predicate isBusyDelayCall(FunctionCall fc) {
  fc.getTarget().getName() = "mdelay"
}

from FunctionCall fc, Function f
where
  isBusyDelayCall(fc) and
  f = fc.getEnclosingFunction() and
  (
    f.getName().matches("%_resume%") or
    f.getName().matches("%_suspend%") or
    f.getName().matches("%_probe%") or
    f.getName().matches("%_init%") or
    f.getName().matches("%_open%") or
    f.getName().matches("%_release%") or
    f.getName().matches("%_remove%")
  ) and
  not (
    f.getName().matches("%irq%") or
    f.getName().matches("%_isr%") or
    f.getName().matches("%critical_section%") or
    f.getName().matches("%_atomic%")
  )
select fc,
  "mdelay() called inside a sleepable callback (" + f.getName() +
    "); replace with msleep() / usleep_range()."
