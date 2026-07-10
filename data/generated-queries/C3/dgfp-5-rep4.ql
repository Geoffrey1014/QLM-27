/**
 * @name Busy-wait (mdelay/udelay) in sleepable context (delay-gfp pattern)
 * @description Detects calls to a busy-wait kernel primitive
 *              (mdelay/udelay/__udelay/__const_udelay) whose enclosing
 *              function is provably sleepable, either by name shape
 *              (probe/init/resume/suspend/handler/work/thread) or by
 *              evidence that the function itself calls a sleeping
 *              allocator (kzalloc/kmalloc/kcalloc/vmalloc/kvmalloc).
 *              Such busy-waits waste CPU cycles where usleep_range() or
 *              msleep() would cooperatively yield. Pattern derived from
 *              upstream commit 9f96b9b7d836 ("PCI: endpoint: Replace
 *              mdelay with usleep_range() in pci_epf_test_write()"),
 *              one of the Bai/DSAC delay-gfp findings (ATC 2018 family).
 *
 *              The query gates on:
 *                P1. busy-wait call: mdelay/udelay/__udelay/__const_udelay.
 *                P2. atomic-context detector: function name signals IRQ /
 *                    NMI / locked / tasklet context, OR function calls a
 *                    spin_lock-family / preempt_disable / rcu_read_lock
 *                    primitive — these are correct uses of mdelay().
 *                P3. allocator-evidence: function calls a sleeping
 *                    allocator (kzalloc family).
 *                P4. sleepable-context detector: function is NOT atomic
 *                    AND (calls a sleeping allocator OR has a callback-
 *                    style name typically scheduled in process context).
 *                P5. combine: busy-wait call whose enclosing function is
 *                    sleepable.
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3/c3/delay-gfp-busywait-in-sleepable
 * @tags reliability
 *       delay-gfp
 *       performance
 */

import cpp

/* P1: busy-wait kernel primitives that we want to flag. */
predicate isBusyWaitCall(FunctionCall fc) {
  exists(string n | n = fc.getTarget().getName() |
    n = "mdelay" or n = "udelay" or n = "__udelay" or n = "__const_udelay"
  )
}

/* P2: atomic context — name or lock-evidence. mdelay() is fine here. */
predicate isAtomicContextFunction(Function f) {
  f.getName().matches("%irq_handler%") or
  f.getName().matches("%_isr%") or
  f.getName().matches("%_interrupt%") or
  f.getName().matches("%_nmi%") or
  f.getName().matches("%locked%") or
  f.getName().matches("%_tasklet%") or
  exists(FunctionCall sc |
    sc.getEnclosingFunction() = f and
    (sc.getTarget().getName() = "spin_lock" or
     sc.getTarget().getName() = "spin_lock_irq" or
     sc.getTarget().getName() = "spin_lock_irqsave" or
     sc.getTarget().getName() = "spin_lock_bh" or
     sc.getTarget().getName() = "local_irq_disable" or
     sc.getTarget().getName() = "preempt_disable" or
     sc.getTarget().getName() = "rcu_read_lock"))
}

/* P3: allocator evidence — calling a sleeping allocator proves the
 *     function is allowed to sleep (GFP_KERNEL contract). */
predicate callsSleepingAllocator(Function f) {
  exists(FunctionCall ac |
    ac.getEnclosingFunction() = f and
    (ac.getTarget().getName() = "kzalloc" or
     ac.getTarget().getName() = "kmalloc" or
     ac.getTarget().getName() = "kcalloc" or
     ac.getTarget().getName() = "vmalloc" or
     ac.getTarget().getName() = "kvmalloc"))
}

/* P4: sleepable context — not atomic, AND either allocator evidence or
 *     callback-name evidence. The pci_epf_test_write/cmd_handler patterns
 *     are explicitly listed since they are the canonical seed names. */
predicate isSleepableContextFunction(Function f) {
  not isAtomicContextFunction(f) and
  (callsSleepingAllocator(f) or
   f.getName().matches("%_probe%") or
   f.getName().matches("%_init%") or
   f.getName().matches("%_resume%") or
   f.getName().matches("%_suspend%") or
   f.getName().matches("%_handler%") or
   f.getName().matches("%_work%") or
   f.getName().matches("%_workqueue%") or
   f.getName().matches("%_thread%") or
   f.getName().matches("%pci_epf_test_write%") or
   f.getName().matches("%_cmd_handler%"))
}

/* P5: combine. */
predicate busyWaitInSleepableContext(FunctionCall fc) {
  isBusyWaitCall(fc) and isSleepableContextFunction(fc.getEnclosingFunction())
}

from FunctionCall fc
where busyWaitInSleepableContext(fc)
select fc,
       "Busy-wait '" + fc.getTarget().getName() + "' called inside '" +
       fc.getEnclosingFunction().getName() +
       "', which is sleepable (calls a sleeping allocator or has a sleepable-callback name); prefer usleep_range()/msleep()."
