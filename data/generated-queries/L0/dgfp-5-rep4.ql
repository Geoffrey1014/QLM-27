/**
 * @name mdelay() used in sleepable context (delay-gfp pattern) [L0]
 * @description Detects mdelay() calls (busy-wait) whose enclosing function
 *              does NOT look like an atomic-context entry point (irq/
 *              handler/isr/interrupt/atomic/nmi/tasklet/softirq/locked/
 *              critical_section) AND does not hold any spin/preempt/
 *              irq/rcu lock at function scope. Pattern from commit
 *              9f96b9b7d836 ("PCI: endpoint: Replace mdelay with
 *              usleep_range() in pci_epf_test_write()"), where
 *              pci_epf_test_write() -- reached from a workqueue handler
 *              (INIT_DELAYED_WORK) -- busy-waits 1 ms in sleepable
 *              process context.
 *
 *              L0 zero-shot variant: exactly one helper predicate
 *              (the raw mdelay call); the atomic-context exclusions
 *              are inlined in the assembly where-clause. No
 *              compile-repair or assemble-refine loops.
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3/l0/delay-gfp-mdelay-in-sleepable-pciepf
 * @tags reliability
 *       delay-gfp
 *       performance
 */

import cpp

predicate isBusyDelayCall(FunctionCall fc) {
  fc.getTarget().getName() = "mdelay"
}

from FunctionCall fc, Function caller
where
  isBusyDelayCall(fc) and
  caller = fc.getEnclosingFunction() and
  not (caller.getName().matches("%irq%") or
       caller.getName().matches("%handler%") or
       caller.getName().matches("%_isr%") or
       caller.getName().matches("%interrupt%") or
       caller.getName().matches("%atomic%") or
       caller.getName().matches("%nmi%") or
       caller.getName().matches("%tasklet%") or
       caller.getName().matches("%softirq%") or
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
       "mdelay() in sleepable context (" + caller.getName() +
       "); should be usleep_range()/msleep()"
