/**
 * @name  rq3-l0-dgfp-5-rep1
 * @id    cpp/rq3/l0/dgfp-5-rep1
 * @kind  problem
 * @problem.severity warning
 * @description RQ4 cell L0 (zero-shot compositional, N_PRED=1, no refine).
 *              Flags mdelay()/udelay() busy-wait calls whose enclosing
 *              function has a sleepable-context name (probe/init/resume/
 *              suspend/write/handler/device_init) and does not disable
 *              preemption/hold a spinlock/run in IRQ context.
 *              Seed: 9f96b9b7d836 (pci_epf_test_write mdelay->usleep_range).
 */

import cpp

predicate isBusyWaitInSleepableContext(FunctionCall fc) {
  exists(Function callee, Function enclosing |
    callee = fc.getTarget() and enclosing = fc.getEnclosingFunction() |
    (
      callee.getName() = "mdelay" or
      callee.getName() = "udelay" or
      callee.getName() = "ndelay" or
      callee.getName() = "__const_udelay" or
      callee.getName() = "__udelay"
    ) and
    (
      enclosing.getName().matches("%_probe%") or
      enclosing.getName().matches("%_init%") or
      enclosing.getName().matches("%_resume%") or
      enclosing.getName().matches("%_suspend%") or
      enclosing.getName().matches("%_write%") or
      enclosing.getName().matches("%_handler%") or
      enclosing.getName().matches("%device_init%")
    ) and
    not enclosing.getName().matches("%_irq_handler%") and
    not enclosing.getName().matches("%_isr%") and
    not enclosing.getName().matches("%_interrupt%") and
    not enclosing.getName().matches("%irq_handler%") and
    not exists(FunctionCall lock |
      lock.getEnclosingFunction() = enclosing and
      (
        lock.getTarget().getName() = "spin_lock" or
        lock.getTarget().getName() = "spin_lock_irq" or
        lock.getTarget().getName() = "spin_lock_irqsave" or
        lock.getTarget().getName() = "spin_lock_bh" or
        lock.getTarget().getName() = "local_irq_disable" or
        lock.getTarget().getName() = "preempt_disable" or
        lock.getTarget().getName() = "rcu_read_lock"
      )
    )
  )
}

from FunctionCall fc
where isBusyWaitInSleepableContext(fc)
select fc,
  "mdelay()/udelay() busy-wait in a sleepable context (probe/init/resume/suspend/write handler); consider msleep() or usleep_range()."
