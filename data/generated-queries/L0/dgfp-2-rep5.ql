/**
 * @name  rq3-l0-dgfp-2-rep5
 * @id    cpp/rq3/l0/dgfp-2-rep5
 * @kind  problem
 * @problem.severity warning
 * @description Zero-shot compositional (L0) query for RQ4 delay-gfp pattern.
 *              Single predicate + assembly (no per-predicate refine, no
 *              assemble-refine). Flags mdelay()/udelay()/ndelay() calls
 *              inside sleepable (probe/init/resume/suspend/device_init)
 *              callers that are not IRQ handlers and do not sit inside
 *              a spin-lock/preempt-disabled/RCU region.
 *              Seed: e9acf05255cb (cavium cpt cpt_device_init).
 */

import cpp

predicate busyDelayInSleepableContext(FunctionCall fc) {
  fc.getTarget().getName() in ["mdelay", "udelay", "ndelay", "__udelay", "__const_udelay"] and
  exists(Function caller | caller = fc.getEnclosingFunction() |
    (
      caller.getName().matches("%probe%") or
      caller.getName().matches("%resume%") or
      caller.getName().matches("%suspend%") or
      caller.getName().matches("%device_init%") or
      caller.getName().matches("%_init") or
      caller.getName().matches("init_%")
    ) and
    not caller.getName().matches("%irq%") and
    not caller.getName().matches("%handler%") and
    not caller.getName().matches("%_isr%") and
    not caller.getName().matches("%interrupt%") and
    not caller.getName().matches("%tasklet%") and
    not caller.getName().matches("%atomic%") and
    not exists(FunctionCall lc |
      lc.getEnclosingFunction() = caller and
      lc.getTarget().getName() in [
        "spin_lock", "spin_lock_irq", "spin_lock_irqsave",
        "spin_lock_bh", "raw_spin_lock", "raw_spin_lock_irqsave",
        "local_irq_disable", "local_bh_disable",
        "preempt_disable", "rcu_read_lock", "rcu_read_lock_bh"
      ]
    )
  )
}

from FunctionCall fc, Function caller
where busyDelayInSleepableContext(fc) and caller = fc.getEnclosingFunction()
select fc,
  "busy-wait delay (" + fc.getTarget().getName() +
  ") in sleepable context " + caller.getName() +
  "() -- prefer msleep()/usleep_range()."
