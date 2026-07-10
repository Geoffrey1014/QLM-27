/**
 * @name mdelay() used in sleepable context (delay-gfp pattern) [L0]
 * @description Detects calls to mdelay() -- a busy-wait millisecond delay --
 *              whose enclosing function does NOT look like an atomic-context
 *              entry point (irq handler / nmi / tasklet / softirq / atomic /
 *              spinlock-held critical section). In sleepable contexts (probes,
 *              workqueue handlers, PM callbacks, plain syscalls) the sleeping
 *              primitive usleep_range() or msleep() should be used instead.
 *
 *              Pattern from commit 9f96b9b7d836 ("PCI: endpoint: Replace
 *              mdelay with usleep_range() in pci_epf_test_write()").
 *
 *              L0 zero-shot compositional variant: exactly ONE helper
 *              predicate (isMillisecondBusyDelay) is defined; the
 *              sleepable/atomic context selection is inlined in the
 *              assembly where-clause per the L0 ablation (N_PRED=1).
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3/l0/delay-gfp-mdelay-in-sleepable-rep5
 * @tags reliability
 *       delay-gfp
 *       performance
 */

import cpp

predicate isMillisecondBusyDelay(FunctionCall fc) {
  fc.getTarget().getName() = "mdelay"
}

from FunctionCall fc, Function caller
where
  isMillisecondBusyDelay(fc) and
  caller = fc.getEnclosingFunction() and
  not caller.getName().matches("%irq%") and
  not caller.getName().matches("%handler%") and
  not caller.getName().matches("%nmi%") and
  not caller.getName().matches("%tasklet%") and
  not caller.getName().matches("%softirq%") and
  not caller.getName().matches("%atomic%") and
  not caller.getName().matches("%critical_section%") and
  not caller.getName().matches("%_locked%") and
  not caller.getName().matches("%locked_%") and
  not exists(FunctionCall lk |
    lk.getEnclosingFunction() = caller and
    lk.getTarget().getName() = "spin_lock")
select fc,
  "mdelay() called in sleepable context (" + caller.getName() +
  "); use usleep_range()/msleep() instead"
