/**
 * @name Busy-wait mdelay() in non-atomic context
 * @description Calls to mdelay() busy-wait the CPU for the entire delay.
 *              Unless the call is in atomic context (IRQ handler, holding
 *              a spinlock, NMI, tasklet, etc.) it should be replaced with
 *              a sleeping primitive such as msleep() or usleep_range(),
 *              which yield the CPU instead of spinning.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-dgfp-5
 */

import cpp

/**
 * Holds if `f` is a likely atomic-context function where mdelay() is
 * acceptable: ISR handlers, spinlock-holding helpers, NMI handlers,
 * tasklet callbacks, etc. We use a conservative name-based heuristic;
 * the goal here is to suppress obvious atomic-context mdelay() usages,
 * not to perfectly model kernel context. Anything else is treated as
 * non-atomic.
 */
predicate isLikelyAtomicContext(Function f) {
  exists(string n | n = f.getName().toLowerCase() |
    n.matches("%_isr") or
    n.matches("%_irq%") or
    n.matches("%_handler") or
    n.matches("%_nmi%") or
    n.matches("%_interrupt") or
    n.matches("%spin_%") or
    n.matches("%_atomic%") or
    n.matches("%_tasklet%") or
    n.matches("%_callback")
  )
}

/**
 * Holds if `f` is a worker/probe/resume/open/write-style entry point
 * — i.e. process / workqueue / sysfs / file-ops context that is
 * never called with interrupts disabled.  Used only to make the
 * select message a little more informative; the where-clause does
 * not require it.
 */
predicate isLikelyProcessContext(Function f) {
  exists(string n | n = f.getName().toLowerCase() |
    n.matches("%_probe") or
    n.matches("%_resume") or
    n.matches("%_suspend") or
    n.matches("%_open") or
    n.matches("%_release") or
    n.matches("%_write") or
    n.matches("%_read") or
    n.matches("%_ioctl") or
    n.matches("%_work") or
    n.matches("%_worker") or
    n.matches("%_thread") or
    n.matches("%_init")
  )
}

from FunctionCall fc, Function callee, Function enclosing
where
  callee = fc.getTarget() and
  callee.getName() = "mdelay" and
  enclosing = fc.getEnclosingFunction() and
  // skip plausibly-atomic helpers
  not isLikelyAtomicContext(enclosing)
select fc,
  "mdelay() busy-waits in non-atomic-looking function '" +
  enclosing.getName() + "'; consider msleep() or usleep_range() instead."
