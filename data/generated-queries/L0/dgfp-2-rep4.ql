/**
 * @name mdelay() used in sleepable context (delay-gfp pattern) [L0]
 * @description Detects mdelay() calls (busy-wait) whose enclosing function
 *              looks like a sleepable-context entry point (probe/init/
 *              resume/suspend/work) and does NOT look like an atomic-context
 *              entry point (irq/handler/isr/interrupt/atomic/nmi/tasklet/
 *              locked/critical_section) nor holds any spin/preempt/irq/rcu
 *              lock at function scope. Pattern from commit e9acf05255cb
 *              ("crypto: cavium - Replace mdelay with msleep in
 *              cpt_device_init"), where cpt_device_init() (called from the
 *              PCI .probe callback cpt_probe()) busy-waits 100 ms in
 *              sleepable process context.
 *
 *              L0 zero-shot variant: exactly one helper predicate
 *              (busy-delay call in a sleepable-named function); the
 *              atomic-context exclusions are inlined in the assembly
 *              where-clause. No compile-repair or assemble-refine loops.
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3/l0/delay-gfp-mdelay-in-sleepable-cpt
 * @tags reliability
 *       delay-gfp
 *       performance
 */

import cpp

predicate isBusyDelayInSleepable(FunctionCall fc) {
  fc.getTarget().getName() = "mdelay" and
  exists(fc.getArgument(0).getValue().toInt()) and
  fc.getArgument(0).getValue().toInt() >= 10 and
  exists(Function caller |
    caller = fc.getEnclosingFunction() and
    (caller.getName().matches("%probe%") or
     caller.getName().matches("%_init%") or
     caller.getName().matches("%resume%") or
     caller.getName().matches("%suspend%") or
     caller.getName().matches("%device_init%") or
     caller.getName().matches("%_work%") or
     caller.getName().matches("%_worker%")))
}

from FunctionCall fc, Function caller
where
  isBusyDelayInSleepable(fc) and
  caller = fc.getEnclosingFunction() and
  not (caller.getName().matches("%irq%") or
       caller.getName().matches("%handler%") or
       caller.getName().matches("%_isr%") or
       caller.getName().matches("%interrupt%") or
       caller.getName().matches("%atomic%") or
       caller.getName().matches("%nmi%") or
       caller.getName().matches("%tasklet%") or
       caller.getName().matches("%_locked%") or
       caller.getName().matches("%critical_section%")) and
  not exists(FunctionCall lc |
    lc.getEnclosingFunction() = caller and
    (lc.getTarget().getName() = "spin_lock" or
     lc.getTarget().getName() = "spin_lock_irq" or
     lc.getTarget().getName() = "spin_lock_irqsave" or
     lc.getTarget().getName() = "spin_lock_bh" or
     lc.getTarget().getName() = "local_irq_disable" or
     lc.getTarget().getName() = "preempt_disable" or
     lc.getTarget().getName() = "rcu_read_lock"))
select fc,
       "mdelay(" + fc.getArgument(0).getValue() +
       ") in sleepable context (" + caller.getName() +
       "); consider msleep() instead"
