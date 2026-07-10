/**
 * @name Busy-wait mdelay used in sleepable context
 * @description Detects calls to mdelay() with a relatively long duration inside
 *              functions that are only reachable from sleepable entry points
 *              (probe/init/ioctl/work handlers/etc.). In such contexts, msleep()
 *              should be used instead of mdelay() to avoid wasting CPU cycles
 *              busy-waiting. This is the bug class fixed by commits replacing
 *              mdelay(N) with msleep(N) in non-atomic paths.
 * @kind problem
 * @problem.severity warning
 * @id cpp/mdelay-in-sleepable-context
 * @tags performance
 *       correctness
 */

import cpp
import semmle.code.cpp.controlflow.IRGuards

/**
 * A call to a busy-wait delay primitive: mdelay/__mdelay.
 * udelay/ndelay are intentionally excluded — they're for short busy waits
 * where msleep granularity (jiffies) wouldn't fit.
 */
class BusyDelayCall extends FunctionCall {
  BusyDelayCall() {
    this.getTarget().getName() = ["mdelay", "__mdelay"]
  }

  int getDelayMs() {
    result = this.getArgument(0).getValue().toInt()
  }
}

/**
 * A function whose name suggests an atomic-context callee:
 * IRQ handlers, tasklets, timers, anything that runs with preemption off
 * or under a spinlock by API contract.
 */
predicate isAtomicContextFunction(Function f) {
  exists(string n | n = f.getName() |
    n.matches("%_irq") or
    n.matches("%_irq_handler") or
    n.matches("%_isr") or
    n.matches("%_interrupt") or
    n.matches("%_tasklet") or
    n.matches("%_timer_fn") or
    n.matches("%_timer_cb") or
    n.matches("%_softirq") or
    n.matches("%_nmi") or
    n.matches("%_rcu_%") or
    n = "handle_irq" or
    n = "do_IRQ"
  )
}

/**
 * Heuristic: a function whose name suggests a sleepable entry point
 * (probe/init/ioctl/workqueue/sysfs etc).
 */
predicate isSleepableContextFunction(Function f) {
  exists(string n | n = f.getName() |
    n.matches("%_probe") or
    n = "probe" or
    n.matches("%_init") or
    n.matches("init_%") or
    n.matches("%_open") or
    n.matches("%_release") or
    n.matches("%_ioctl") or
    n.matches("%_work") or
    n.matches("%_work_handler") or
    n.matches("%_worker") or
    n.matches("%_store") or
    n.matches("%_show") or
    n.matches("%_setup") or
    n.matches("%_remove")
  )
}

/**
 * Function transitively reachable as a callee of f, up to a small depth.
 */
predicate reachableFrom(Function root, Function f, int depth) {
  f = root and depth = 0
  or
  exists(Function mid, FunctionCall fc |
    reachableFrom(root, mid, depth - 1) and
    depth <= 3 and
    fc.getEnclosingFunction() = mid and
    fc.getTarget() = f
  )
}

/**
 * f is "sleepable": either its own name fits a sleepable entry-point pattern,
 * or it is statically reachable from such an entry point, and no caller chain
 * looks like an atomic context.
 */
predicate inSleepableContext(Function f) {
  (
    isSleepableContextFunction(f)
    or
    exists(Function entry |
      isSleepableContextFunction(entry) and
      reachableFrom(entry, f, _)
    )
  ) and
  not exists(Function atomic |
    isAtomicContextFunction(atomic) and
    reachableFrom(atomic, f, _)
  )
}

/**
 * Holds if the call site is dominated by a spin_lock-style call within the
 * same function (very local check; conservative — only excludes obvious
 * intra-function locked regions).
 */
predicate underLocalSpinLock(BusyDelayCall bdc) {
  exists(FunctionCall lockCall |
    lockCall.getEnclosingFunction() = bdc.getEnclosingFunction() and
    lockCall.getTarget().getName().matches("spin_lock%") and
    not lockCall.getTarget().getName().matches("spin_lock_init%") and
    lockCall.getLocation().getStartLine() < bdc.getLocation().getStartLine()
  ) and
  not exists(FunctionCall unlockCall |
    unlockCall.getEnclosingFunction() = bdc.getEnclosingFunction() and
    unlockCall.getTarget().getName().matches("spin_unlock%") and
    unlockCall.getLocation().getStartLine() < bdc.getLocation().getStartLine()
  )
}

from BusyDelayCall bdc, Function enclosing, int ms
where
  enclosing = bdc.getEnclosingFunction() and
  ms = bdc.getDelayMs() and
  // Only flag delays that are long enough to matter for scheduler granularity.
  ms >= 10 and
  inSleepableContext(enclosing) and
  not underLocalSpinLock(bdc)
select bdc,
  "Busy-wait mdelay(" + ms.toString() + ") in sleepable function '" +
    enclosing.getName() + "'; use msleep() instead to avoid wasting CPU."
