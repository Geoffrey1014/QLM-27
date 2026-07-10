/**
 * @name mdelay() used in sleepable (workqueue / write / probe) context (delay-gfp)
 * @description Detects calls to mdelay() — a busy-wait primitive — whose
 *              enclosing function runs in process / sleepable context (worker
 *              handlers, workqueue callbacks, driver probe, .write/.read
 *              dispatch entry points, PM resume/suspend), where the sleeping
 *              equivalent usleep_range() or msleep() should be used instead.
 *              Pattern derived from upstream commit 9f96b9b7d836 ("PCI:
 *              endpoint: Replace mdelay with usleep_range() in
 *              pci_epf_test_write()"), part of the Bai/DSAC delay-gfp family
 *              (USENIX ATC 2018).
 *
 *              Gate (compositional):
 *                P1. mdelay() call (any argument).
 *                P2. enclosing function is NOT atomic-context (irq handler /
 *                    isr / interrupt / nmi / tasklet / holds spin_lock /
 *                    preempt_disable / rcu_read_lock).
 *                P3. enclosing function's name matches a sleepable-context
 *                    entry point (write / work / probe / init / resume /
 *                    suspend / cmd_handler).
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3/c3/delay-gfp-mdelay-in-sleepable
 * @tags reliability
 *       delay-gfp
 *       performance
 */

import cpp

/* P1: any mdelay() call. The argument value is intentionally NOT inspected,
 *     because the seed bug (9f96b9b7d836) is mdelay(1) inside a workqueue
 *     dispatch path — the magnitude of the delay is not the discriminator;
 *     the calling context is. */
predicate isBusyDelayCall(FunctionCall fc) {
  fc.getTarget().getName() = "mdelay"
}

/* P2: enclosing function is atomic-context. Combination of name patterns
 *     (irq handler / isr / interrupt / nmi / tasklet) and explicit
 *     atomic-region API calls (spin_lock*, preempt_disable, rcu_read_lock,
 *     local_irq_disable). Excluding these keeps the query silent on the
 *     genuinely-correct mdelay() sites that motivate the underscore-prefixed
 *     `handler` / `interrupt` shapes. */
predicate isAtomicContextFunction(Function f) {
  f.getName().matches("%irq_handler%") or
  f.getName().matches("%_isr%") or
  f.getName().matches("%_isr_%") or
  f.getName().matches("%_interrupt%") or
  f.getName().matches("%_atomic%") or
  f.getName().matches("%atomic_%") or
  f.getName().matches("%_nmi%") or
  f.getName().matches("%nmi_%") or
  f.getName().matches("%_tasklet%") or
  f.getName().matches("%tasklet_%") or
  exists(FunctionCall fc |
    fc.getEnclosingFunction() = f and
    (
      fc.getTarget().getName() = "spin_lock" or
      fc.getTarget().getName() = "spin_lock_irq" or
      fc.getTarget().getName() = "spin_lock_irqsave" or
      fc.getTarget().getName() = "spin_lock_bh" or
      fc.getTarget().getName() = "local_irq_disable" or
      fc.getTarget().getName() = "preempt_disable" or
      fc.getTarget().getName() = "rcu_read_lock"
    )
  )
}

/* P3: enclosing function's name looks like a sleepable-context entry point:
 *     workqueue handler (work / cmd_handler), the .write/.read endpoint
 *     dispatch (the seed shape), PM resume/suspend callback, driver probe
 *     or *_init helpers. Explicitly excludes atomic-context functions so
 *     name overlap (e.g. work_handler) does not flip the verdict. */
predicate isSleepableContextByName(Function f) {
  not isAtomicContextFunction(f) and
  (
    f.getName().matches("%write%") or
    f.getName().matches("%work%") or
    f.getName().matches("%probe%") or
    f.getName().matches("%_init%") or
    f.getName().matches("%init_%") or
    f.getName().matches("%resume%") or
    f.getName().matches("%suspend%") or
    f.getName().matches("%cmd_handler%")
  )
}

from FunctionCall fc, Function caller
where
  isBusyDelayCall(fc) and
  caller = fc.getEnclosingFunction() and
  isSleepableContextByName(caller) and
  not isAtomicContextFunction(caller)
select fc,
       "mdelay() busy-wait in sleepable context (" + caller.getName() +
       "); should be usleep_range() / msleep()"
