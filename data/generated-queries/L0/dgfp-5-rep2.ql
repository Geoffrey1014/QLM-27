/**
 * @name mdelay() used in sleepable context (delay-gfp pattern)
 * @description Detects calls to mdelay() -- a busy-wait primitive --
 *              whose enclosing function is not recognisably in atomic
 *              context (IRQ handler, NMI, tasklet, softirq, spinlock-held
 *              helper). In sleepable contexts the sleeping primitive
 *              usleep_range() or msleep() should be used instead.
 *
 *              Pattern derived from commit 9f96b9b7d836 ("PCI: endpoint:
 *              Replace mdelay with usleep_range() in
 *              pci_epf_test_write()"), delay-gfp family.
 * @kind problem
 * @problem.severity warning
 * @id cpp/dgfp-5-rep2-l0
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
  not caller.getName().matches("%irq%") and
  not caller.getName().matches("%nmi%") and
  not caller.getName().matches("%tasklet%") and
  not caller.getName().matches("%softirq%") and
  not caller.getName().matches("%_locked%") and
  not caller.getName().matches("%locked_%") and
  not caller.getName().matches("%atomic%") and
  not exists(FunctionCall lock |
    lock.getEnclosingFunction() = caller and
    lock.getTarget().getName() = "spin_lock" and
    lock.getLocation().getStartLine() < fc.getLocation().getStartLine())
select fc,
  "mdelay() in sleepable context (" + caller.getName() +
  "); should be usleep_range()/msleep()"
