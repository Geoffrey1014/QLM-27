/**
 * @name  rq3-c3-dgfp-2-rep1
 * @id    cpp/rq3/c3/dgfp-2-rep1
 * @kind  problem
 * @problem.severity warning
 * @description Full JAWS pipeline (compositional + POC + verifier-v1) for
 *              RQ3 cell C3. Flags mdelay()/udelay() busy-wait calls in
 *              sleepable (probe/init/resume/suspend) context, where
 *              msleep() / usleep_range() should be used instead.
 *              Seed: e9acf05255cb (cavium cpt cpt_device_init).
 */

import cpp

predicate isBusyWaitCall(FunctionCall fc) {
  exists(Function callee | callee = fc.getTarget() |
    callee.getName() = "mdelay" or
    callee.getName() = "udelay" or
    callee.getName() = "ndelay" or
    callee.getName() = "__const_udelay" or
    callee.getName() = "__udelay"
  )
}

predicate isAtomicContextFunction(Function f) {
  f.getName().matches("%_irq_handler%") or
  f.getName().matches("%_isr%") or
  f.getName().matches("%_interrupt%") or
  f.getName().matches("%irq_handler%") or
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

predicate isSleepableContextFunction(Function f) {
  not isAtomicContextFunction(f) and
  (
    f.getName().matches("%_probe%") or
    f.getName().matches("%_init%") or
    f.getName().matches("%_resume%") or
    f.getName().matches("%_suspend%") or
    f.getName().matches("%device_init%")
  )
}

predicate busyWaitInSleepableContext(FunctionCall fc) {
  isBusyWaitCall(fc) and
  isSleepableContextFunction(fc.getEnclosingFunction())
}

from FunctionCall fc
where busyWaitInSleepableContext(fc)
select fc,
  "mdelay()/udelay() busy-wait in a sleepable context (probe/init/resume/suspend); consider msleep() or usleep_range()."
