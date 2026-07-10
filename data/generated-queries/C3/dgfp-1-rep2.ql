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
 * @id qlm/dgfp-1-rep2
 * @tags reliability
 *       performance
 *       linux-kernel
 */

import cpp

predicate isBusyDelayCall(FunctionCall fc) {
  fc.getTarget().getName() = "mdelay"
}

predicate inSleepableNamedFunction(FunctionCall fc) {
  exists(Function f |
    fc.getEnclosingFunction() = f and
    (
      f.getName().matches("%_resume%") or
      f.getName().matches("%_suspend%") or
      f.getName().matches("%_probe%") or
      f.getName().matches("%_init%") or
      f.getName().matches("%_open%") or
      f.getName().matches("%_release%") or
      f.getName().matches("%_remove%")
    )
  )
}

predicate inAtomicNamedFunction(FunctionCall fc) {
  exists(Function f |
    fc.getEnclosingFunction() = f and
    (
      f.getName().matches("%irq%") or
      f.getName().matches("%_isr%") or
      f.getName().matches("%critical_section%") or
      f.getName().matches("%_atomic%")
    )
  )
}

from FunctionCall fc, Function f
where
  isBusyDelayCall(fc) and
  f = fc.getEnclosingFunction() and
  inSleepableNamedFunction(fc) and
  not inAtomicNamedFunction(fc)
select fc,
  "mdelay() called inside a sleepable callback (" + f.getName() +
    "); replace with msleep() / usleep_range()."
