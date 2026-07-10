/**
 * @name  rq3-l0-dgfp-2-rep1
 * @id    cpp/rq3/l0/dgfp-2-rep1
 * @kind  problem
 * @problem.severity warning
 * @description Zero-shot compositional (L0) query for RQ4 delay-gfp pattern.
 *              Single predicate + assembly (no per-predicate refine, no
 *              assemble-refine). Flags mdelay()/udelay()/ndelay() calls
 *              inside sleepable (probe/init/resume/suspend/device_init)
 *              functions that are not IRQ handlers and do not sit inside
 *              a spin-lock/preempt-disabled region.
 *              Seed: e9acf05255cb (cavium cpt cpt_device_init).
 */

import cpp

predicate busyWaitInSleepableContext(FunctionCall fc) {
  (
    fc.getTarget().getName() = "mdelay" or
    fc.getTarget().getName() = "udelay" or
    fc.getTarget().getName() = "ndelay" or
    fc.getTarget().getName() = "__const_udelay" or
    fc.getTarget().getName() = "__udelay"
  )
  and exists(Function enclosing | enclosing = fc.getEnclosingFunction() |
    (
      enclosing.getName().matches("%_probe%") or
      enclosing.getName().matches("%_init%") or
      enclosing.getName().matches("%_resume%") or
      enclosing.getName().matches("%_suspend%") or
      enclosing.getName().matches("%device_init%")
    )
    and not enclosing.getName().matches("%_irq_handler%")
    and not enclosing.getName().matches("%_isr%")
    and not enclosing.getName().matches("%_interrupt%")
    and not enclosing.getName().matches("%irq_handler%")
    and not exists(FunctionCall lockfc |
      lockfc.getEnclosingFunction() = enclosing and
      (
        lockfc.getTarget().getName() = "spin_lock" or
        lockfc.getTarget().getName() = "spin_lock_irq" or
        lockfc.getTarget().getName() = "spin_lock_irqsave" or
        lockfc.getTarget().getName() = "spin_lock_bh" or
        lockfc.getTarget().getName() = "local_irq_disable" or
        lockfc.getTarget().getName() = "preempt_disable" or
        lockfc.getTarget().getName() = "rcu_read_lock"
      )
    )
  )
}

from FunctionCall fc
where busyWaitInSleepableContext(fc)
select fc,
  "mdelay()/udelay() busy-wait in a sleepable context (probe/init/resume/suspend); consider msleep() or usleep_range()."
