/**
 * @name mdelay() used in sleepable context (delay-gfp pattern)
 * @description Detects calls to mdelay() — a busy-wait primitive — whose
 *              enclosing function is NOT recognisably in atomic context
 *              (IRQ handler, NMI, tasklet, spinlock-held helper). In
 *              sleepable contexts (workqueue handlers, PM callbacks,
 *              probe, syscall, plain helpers), the sleeping primitive
 *              usleep_range() or msleep() should be used instead, to
 *              avoid wasting CPU cycles by busy-waiting.
 *
 *              Pattern derived from commit 9f96b9b7d836 ("PCI: endpoint:
 *              Replace mdelay with usleep_range() in
 *              pci_epf_test_write()"), in the Bai/DCNS-style
 *              delay-gfp family (ATC 2018).
 *
 *              The query gates on:
 *                P1. an mdelay() call,
 *                P2. enclosing function name does NOT match an
 *                    atomic-context shape (irq/atomic/nmi/_locked/
 *                    tasklet/softirq),
 *                P3. no spin_lock() call precedes the mdelay() inside
 *                    the same function (catches intraprocedural
 *                    spinlock-held cases that the name heuristic
 *                    misses).
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3/c3/delay-gfp-mdelay-in-sleepable
 * @tags reliability
 *       delay-gfp
 *       performance
 */

import cpp

/* P1: any mdelay() call. We do not threshold on the argument value
 * because the seed bug uses mdelay(1) — short busy-waits are *also*
 * inappropriate when the caller is sleepable. */
predicate isBusyDelayCall(FunctionCall fc) {
  fc.getTarget().getName() = "mdelay"
}

/* P2: enclosing function looks like atomic context. Names tested:
 *   - "%irq%"      — IRQ handlers and helpers thereof
 *   - "%atomic%"   — explicit atomic helpers
 *   - "%nmi%"      — NMI callbacks
 *   - "%_locked%" / "%locked_%" — _locked()/locked_()-suffixed helpers
 *     conventionally called with a lock held; the substring "locked"
 *     alone would over-match (e.g. "unlocked").
 *   - "%tasklet%"  — tasklet handlers
 *   - "%softirq%"  — softirq handlers
 * Note: bare "%handler%" is intentionally NOT used — it over-matches
 * sleepable workqueue handlers such as work_handler / cmd_handler. */
predicate inAtomicContextByName(Function f) {
  exists(string n |
    n = f.getName() and
    (n.matches("%irq%") or
     n.matches("%atomic%") or
     n.matches("%nmi%") or
     n.matches("%_locked%") or
     n.matches("%locked_%") or
     n.matches("%tasklet%") or
     n.matches("%softirq%"))
  )
}

/* P3: there is a spin_lock() call earlier in the same function — a
 * cheap intraprocedural approximation of "running with a spinlock
 * held". Catches helpers whose name does not flag the atomic context
 * but which acquire a lock before the mdelay(). */
predicate holdsSpinLockBefore(FunctionCall fc) {
  exists(FunctionCall lock |
    lock.getEnclosingFunction() = fc.getEnclosingFunction() and
    lock.getTarget().getName() = "spin_lock" and
    lock.getLocation().getStartLine() < fc.getLocation().getStartLine()
  )
}

from FunctionCall fc, Function caller
where
  isBusyDelayCall(fc) and
  caller = fc.getEnclosingFunction() and
  not inAtomicContextByName(caller) and
  not holdsSpinLockBefore(fc)
select fc,
       "mdelay() in sleepable context (" + caller.getName() +
       "); should be usleep_range()/msleep()"
