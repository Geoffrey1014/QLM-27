/**
 * @name Busy-wait mdelay() that should be msleep()
 * @description Calls to mdelay() with a delay >= 10 ms busy-wait the CPU
 *              for the entire duration. Unless the call is in atomic context
 *              (IRQ handler, holding spinlock, etc.) it should be replaced
 *              with msleep(), which puts the task to sleep.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-dgfp-1
 */

import cpp

/**
 * Holds if `f` is a likely atomic-context function where mdelay() is
 * acceptable: ISR handlers, spinlock-holding helpers, NMI handlers, etc.
 * We use a conservative name-based heuristic; the goal here is to
 * suppress obvious atomic-context mdelay() usages, not to perfectly
 * model kernel context. Anything else is treated as non-atomic.
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
    n.matches("%_tasklet%")
  )
}

from FunctionCall fc, Function callee, Function enclosing, int ms
where
  callee = fc.getTarget() and
  callee.getName() = "mdelay" and
  enclosing = fc.getEnclosingFunction() and
  // delay value is a compile-time constant >= 10 ms (long enough that a
  // sleep-based wait would be more appropriate than a busy-wait)
  ms = fc.getArgument(0).getValue().toInt() and
  ms >= 10 and
  // skip plausibly-atomic helpers
  not isLikelyAtomicContext(enclosing)
select fc,
  "mdelay(" + ms.toString() +
  ") busy-waits in non-atomic-looking function '" + enclosing.getName() +
  "'; consider msleep() instead."
