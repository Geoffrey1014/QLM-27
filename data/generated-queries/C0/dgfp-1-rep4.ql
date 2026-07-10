/**
 * @name Long mdelay() in sleepable context
 * @description Calls to mdelay()/udelay() with large delay values from functions
 *              that are known to run in process (sleepable) context should be
 *              replaced with msleep()/usleep_range() to avoid wasting CPU cycles
 *              in a busy-wait loop. This pattern was the source of the
 *              wdt87xx_resume() fix (commit e58650b57ee0) and many similar
 *              kernel fixes found by static analyzers such as DCNS.
 * @kind problem
 * @problem.severity warning
 * @id cpp/long-mdelay-in-sleepable-context
 * @tags performance
 *       correctness
 */

import cpp

/**
 * A busy-wait delay function whose argument is in milliseconds (mdelay) or
 * whose effective wait can be long (udelay with a large constant). Replacing
 * with msleep()/usleep_range() is appropriate ONLY in sleepable context.
 */
class BusyWaitCall extends FunctionCall {
  BusyWaitCall() {
    this.getTarget().getName() = ["mdelay", "udelay", "__const_udelay", "__udelay"]
  }

  /**
   * Holds if the busy-wait is "long enough" that converting to msleep is a
   * clear win (>= ~1 ms of wall time). mdelay(N) is N ms. udelay(N) is N us
   * so we require N >= 1000.
   */
  predicate isLong() {
    exists(int v | v = this.getArgument(0).getValue().toInt() |
      this.getTarget().getName() = "mdelay" and v >= 1
      or
      this.getTarget().getName().matches("%udelay") and v >= 1000
    )
  }
}

/**
 * A function that is known to be called only in process (sleepable) context.
 * We use name-based heuristics that match the kernel's well-known sleepable
 * entry points:
 *   - PM callbacks: *_suspend / *_resume / *_freeze / *_thaw / *_poweroff /
 *     *_runtime_suspend / *_runtime_resume
 *   - probe / remove / shutdown driver callbacks
 *   - open / release file_operations callbacks
 *   - ioctl handlers (unlocked_ioctl / compat_ioctl)
 *   - workqueue work handlers (often named *_work / *_worker / do_*_work)
 *   - kthread entry points (*_thread / *_kthread)
 *   - init / exit module functions
 *
 * These functions never run with a spinlock held by their caller (the kernel
 * framework guarantees they are invoked from a process context), so it is
 * safe (and preferable) to use msleep() in them.
 */
class SleepableContextFunction extends Function {
  SleepableContextFunction() {
    exists(string n | n = this.getName() |
      n.matches("%_suspend") or
      n.matches("%_resume") or
      n.matches("%_freeze") or
      n.matches("%_thaw") or
      n.matches("%_poweroff") or
      n.matches("%_runtime_suspend") or
      n.matches("%_runtime_resume") or
      n.matches("%_probe") or
      n.matches("%_remove") or
      n.matches("%_shutdown") or
      n.matches("%_open") or
      n.matches("%_release") or
      n.matches("%_ioctl") or
      n.matches("%_unlocked_ioctl") or
      n.matches("%_compat_ioctl") or
      n.matches("%_work") or
      n.matches("%_worker") or
      n.matches("do_%_work") or
      n.matches("%_thread") or
      n.matches("%_kthread") or
      n.matches("%_init") or
      n.matches("%_exit")
    )
  }
}

/**
 * Holds if `f` (transitively, depth-limited via direct call) reaches a context
 * that disables sleeping. We use a conservative under-approximation: if `f`
 * itself contains a spin_lock/local_irq_disable/preempt_disable BEFORE the
 * delay call in the same function, we exclude that delay. (Cross-procedural
 * atomic-context detection is out of scope for the baseline C0 query.)
 */
predicate hasAtomicGuardBefore(BusyWaitCall c) {
  exists(FunctionCall lockCall |
    lockCall.getEnclosingFunction() = c.getEnclosingFunction() and
    lockCall.getTarget().getName() in [
        "spin_lock", "spin_lock_irq", "spin_lock_irqsave", "spin_lock_bh",
        "raw_spin_lock", "raw_spin_lock_irq", "raw_spin_lock_irqsave",
        "local_irq_disable", "local_irq_save",
        "preempt_disable", "rcu_read_lock", "rcu_read_lock_bh",
        "read_lock", "write_lock", "read_lock_irq", "write_lock_irq",
        "read_lock_irqsave", "write_lock_irqsave"
      ] and
    lockCall.getLocation().getStartLine() < c.getLocation().getStartLine() and
    not exists(FunctionCall unlockCall |
      unlockCall.getEnclosingFunction() = c.getEnclosingFunction() and
      unlockCall.getTarget().getName().matches("%unlock%") and
      unlockCall.getLocation().getStartLine() > lockCall.getLocation().getStartLine() and
      unlockCall.getLocation().getStartLine() < c.getLocation().getStartLine()
    )
  )
}

from BusyWaitCall call, SleepableContextFunction f
where
  call.getEnclosingFunction() = f and
  call.isLong() and
  not hasAtomicGuardBefore(call)
select call,
  "Long busy-wait " + call.getTarget().getName() +
    "() called from sleepable function " + f.getName() +
    "() — consider replacing with msleep()/usleep_range()."
