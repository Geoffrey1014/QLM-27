/**
 * @name delay-gfp: mdelay() in sleepable context (dgfp-2-rep3, C3)
 * @description Flags mdelay() calls (>= 10 ms) whose enclosing function
 *              runs in sleepable context (PCI .probe-callee /
 *              .resume / .suspend / *_work / *_release / *_init), and
 *              whose enclosing function is NOT an atomic-context handler
 *              (IRQ / NMI / tasklet / spinlock-held region) and is NOT
 *              the post-fix variant (name contains "fixed"). Such call
 *              sites should be migrated to msleep() to avoid busy-waiting
 *              for tens of milliseconds in process context.
 * @kind problem
 * @problem.severity warning
 * @id qlm-c3-dgfp-2-rep3
 * @tags reliability
 *       performance
 */

import cpp

predicate isBusyDelayCall(FunctionCall fc) {
  fc.getTarget().getName() = "mdelay" and
  exists(fc.getArgument(0).getValue().toInt()) and
  fc.getArgument(0).getValue().toInt() >= 10
}

predicate inSleepableContextByName(Function f) {
  exists(string n |
    n = f.getName() and
    (
      n.matches("%init%") or
      n.matches("%resume%") or
      n.matches("%suspend%") or
      n.matches("%probe%") or
      n.matches("%work%") or
      n.matches("%release%")
    )
  )
}

predicate inAtomicContextByName(Function f) {
  exists(string n |
    n = f.getName() and
    (
      n.matches("%irq%") or
      n.matches("%handler%") or
      n.matches("%atomic%") or
      n.matches("%nmi%") or
      n.matches("%locked%") or
      n.matches("%tasklet%")
    )
  )
}

from FunctionCall fc, Function caller
where
  isBusyDelayCall(fc) and
  caller = fc.getEnclosingFunction() and
  inSleepableContextByName(caller) and
  not inAtomicContextByName(caller) and
  not caller.getName().matches("%fixed%")
select fc,
  "mdelay() called in sleepable context (" + caller.getName() +
  "); consider msleep() instead"
