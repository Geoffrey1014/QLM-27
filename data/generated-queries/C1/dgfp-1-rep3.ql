/**
 * @name Busy-wait mdelay() in sleepable kernel context
 * @description Detects calls to mdelay() (or equivalent busy-wait delay
 *              primitives) inside functions that are known to execute in
 *              sleepable (non-atomic) process context, such as power-management
 *              resume/suspend callbacks, probe/remove handlers, ioctl/read/write
 *              file_operations, and worker functions. In sleepable context
 *              mdelay() needlessly hogs the CPU; msleep()/usleep_range() should
 *              be used instead.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-dgfp-1
 */

import cpp

/**
 * Names of delay primitives that busy-wait (hot-spin the CPU).
 * These are the call sites we flag.
 */
predicate isBusyWaitDelayName(string name) {
  name = "mdelay" or
  name = "__const_udelay" or
  name = "__udelay"
}

/**
 * Heuristics for "this enclosing function definitely runs in sleepable
 * (non-atomic) process context". We approximate this by recognising
 * the well-known sleepable callback name suffixes used pervasively in
 * Linux kernel drivers and core subsystems.
 */
predicate isSleepableContextFunction(Function f) {
  exists(string n | n = f.getName() |
    // Power-management callbacks (always called from process context).
    n.matches("%_resume%") or
    n.matches("%_suspend%") or
    n.matches("%_freeze%") or
    n.matches("%_thaw%") or
    n.matches("%_poweroff%") or
    n.matches("%_restore%") or
    // Driver model probe/remove/shutdown — process context.
    n.matches("%_probe%") or
    n.matches("%_remove%") or
    n.matches("%_shutdown%") or
    // file_operations / chardev callbacks — process context.
    n.matches("%_open%") or
    n.matches("%_release%") or
    n.matches("%_ioctl%") or
    // Workqueue / kthread / async — sleepable.
    n.matches("%_work%") or
    n.matches("%_worker%") or
    n.matches("%_workfn%") or
    n.matches("%_thread%") or
    n.matches("%_kthread%")
  )
}

/**
 * Exclude obvious atomic-context indicators in the enclosing function:
 * IRQ handlers, tasklets, timers, spin_lock_irqsave regions etc. We use
 * name-suffix exclusions because a monolithic query has no flow analysis.
 */
predicate looksAtomicContext(Function f) {
  exists(string n | n = f.getName() |
    n.matches("%_isr") or
    n.matches("%_irq") or
    n.matches("%_handler") or
    n.matches("%_interrupt") or
    n.matches("%_tasklet") or
    n.matches("%_timer") or
    n.matches("%_callback")
  )
}

from FunctionCall call, Function enclosing, string delayName
where
  delayName = call.getTarget().getName() and
  isBusyWaitDelayName(delayName) and
  enclosing = call.getEnclosingFunction() and
  isSleepableContextFunction(enclosing) and
  not looksAtomicContext(enclosing)
select call,
  "Busy-wait '" + delayName + "' called from sleepable function '" +
    enclosing.getName() + "'; replace with msleep()/usleep_range()."
