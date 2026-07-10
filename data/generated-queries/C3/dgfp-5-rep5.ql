/**
 * @name  rq3-c3-dgfp-5-rep5: mdelay() in sleepable workqueue context
 * @id    cpp/rq3/c3/dgfp-5-rep5
 * @kind  problem
 * @problem.severity warning
 * @description Full QLM pipeline (compositional + POC + verifier-v1) for
 *              RQ3 cell C3. Flags mdelay()/udelay() busy-wait calls in
 *              sleepable contexts (workqueue/handler/PM-callback/probe/init),
 *              where usleep_range() / msleep() should be used instead.
 *              Seed: 9f96b9b7d836 (PCI: endpoint: Replace mdelay with
 *              usleep_range() in pci_epf_test_write()). pci_epf_test_write
 *              is reached from pci_epf_test_cmd_handler() registered with
 *              INIT_DELAYED_WORK() in pci_epf_test_probe() — process /
 *              sleepable context, so busy-waiting is wasteful.
 * @tags reliability
 *       delay-gfp
 *       performance
 */

import cpp

/* P1: mdelay()/udelay()/ndelay() and friends — kernel "busy-wait" delay
 *     primitives. Purely a syntactic call match; the contextual filter is
 *     left to P2/P3. */
predicate isBusyDelayCall(FunctionCall fc) {
  exists(string n |
    n = fc.getTarget().getName() and
    (n = "mdelay" or n = "udelay" or n = "ndelay" or
     n = "__const_udelay" or n = "__udelay")
  )
}

/* P2: enclosing function looks atomic — IRQ/ISR/interrupt handler, NMI,
 *     tasklet/softirq, etc. Busy-wait is legitimate in these contexts. */
predicate inAtomicContextByName(Function f) {
  exists(string n |
    n = f.getName() and
    (n.matches("%_irq%") or
     n.matches("%_isr%") or
     n.matches("%_interrupt%") or
     n.matches("%_tasklet%") or
     n.matches("%_nmi%") or
     n.matches("%irq_handler%"))
  )
}

/* P3: enclosing function looks sleepable — workqueue/handler/PM-callback,
 *     I/O routines (read/write/copy), probe/init paths. Excludes atomic-
 *     looking names so a function named both ways (e.g. resume_irq) is
 *     classified as atomic and kept silent. */
predicate inSleepableContextByName(Function f) {
  not inAtomicContextByName(f) and
  exists(string n |
    n = f.getName() and
    (n.matches("%_write%") or
     n.matches("%_read%") or
     n.matches("%_copy%") or
     n.matches("%_handler%") or
     n.matches("%_work%") or
     n.matches("%_resume%") or
     n.matches("%_suspend%") or
     n.matches("%_probe%") or
     n.matches("%_init%"))
  )
}

from FunctionCall fc, Function caller
where
  isBusyDelayCall(fc) and
  caller = fc.getEnclosingFunction() and
  inSleepableContextByName(caller) and
  not inAtomicContextByName(caller)
select fc,
       "mdelay()/udelay() busy-wait in sleepable context (" + caller.getName() +
       "); consider usleep_range() or msleep()."
