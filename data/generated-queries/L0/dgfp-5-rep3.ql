/**
 * @name mdelay() used in sleepable context (delay-gfp pattern) [L0]
 * @description Detects mdelay() calls whose enclosing function looks like
 *              a sleepable-context entry point (write/read/work/handler/
 *              resume/suspend/probe) and does NOT look like an atomic-
 *              context entry point (irq-handler/isr/nmi/locked/tasklet/
 *              atomic). Pattern from commit 9f96b9b7d836 ("PCI: endpoint:
 *              Replace mdelay with usleep_range() in pci_epf_test_write()").
 *
 *              L0 zero-shot variant: exactly one helper predicate
 *              (busy-delay call recognition); the sleepable/atomic
 *              context filters are inlined in the assembly where-clause.
 * @kind problem
 * @problem.severity warning
 * @id qlm-rq3-l0-delay-gfp-mdelay-in-sleepable-ctx
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
  (caller.getName().matches("%write%") or
   caller.getName().matches("%read%") or
   caller.getName().matches("%work%") or
   caller.getName().matches("%handler%") or
   caller.getName().matches("%resume%") or
   caller.getName().matches("%suspend%") or
   caller.getName().matches("%probe%")) and
  not (caller.getName().matches("%irq%handler%") or
       caller.getName().matches("%isr%") or
       caller.getName().matches("%nmi%") or
       caller.getName().matches("%locked%") or
       caller.getName().matches("%tasklet%") or
       caller.getName().matches("%atomic%"))
select fc,
       "mdelay() in sleepable-context function " + caller.getName() +
       "(); replace with usleep_range()/msleep()"
