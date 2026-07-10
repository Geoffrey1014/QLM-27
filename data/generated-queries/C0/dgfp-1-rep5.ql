/**
 * @name Busy-wait delay in non-atomic process context
 * @description Detects calls to mdelay()/udelay()/ndelay() that occur in
 *              functions that are never invoked from atomic context (e.g.
 *              PM resume/suspend callbacks, probe routines, ioctl handlers,
 *              workqueue handlers). In such cases the busy-wait wastes CPU
 *              cycles and should be replaced with a sleeping variant
 *              (msleep, usleep_range, fsleep) that yields the CPU.
 * @kind problem
 * @problem.severity warning
 * @id cpp/busy-delay-in-process-context
 * @tags performance
 *       correctness
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph

/**
 * A call to a busy-wait delay primitive.
 * These spin on the CPU and do not yield, so they are only appropriate
 * in atomic / interrupt-disabled context.
 */
class BusyDelayCall extends FunctionCall {
  BusyDelayCall() {
    this.getTarget().getName() in [
      "mdelay", "udelay", "ndelay",
      "__mdelay", "__udelay", "__ndelay",
      "__const_udelay"
    ]
  }

  /** The (constant) delay argument value in microseconds, if known. */
  int getDelayUsec() {
    exists(int n | n = this.getArgument(0).getValue().toInt() |
      this.getTarget().getName() = ["udelay", "__udelay", "__const_udelay"] and result = n
      or
      this.getTarget().getName() = ["mdelay", "__mdelay"] and result = n * 1000
      or
      this.getTarget().getName() = ["ndelay", "__ndelay"] and result = n / 1000
    )
  }
}

/**
 * A function that is reasonably known to execute only in non-atomic
 * (sleepable) process context. This is approximated syntactically by the
 * function name suffix / well-known PM and driver-model callback patterns.
 */
predicate isSleepableContextFunction(Function f) {
  exists(string n | n = f.getName() |
    // Power-management callbacks: suspend/resume/freeze/thaw/poweroff/restore
    n.matches("%_suspend") or
    n.matches("%_resume") or
    n.matches("%_freeze") or
    n.matches("%_thaw") or
    n.matches("%_poweroff") or
    n.matches("%_restore") or
    n.matches("%suspend_late") or
    n.matches("%resume_early") or
    n.matches("%suspend_noirq") or // arguable, but PM core invokes with IRQ off only briefly
    // Driver-model callbacks always invoked from process context
    n.matches("%_probe") or
    n.matches("%_remove") or
    n.matches("%_shutdown") or
    // File-operation handlers in process context
    n.matches("%_open") or
    n.matches("%_release") or
    n.matches("%_ioctl") or
    n.matches("%_read") or
    n.matches("%_write") or
    // Workqueue / kthread / deferred work
    n.matches("%_work") or
    n.matches("%_worker") or
    n.matches("%_workfn") or
    n.matches("%_thread") or
    // Module init / exit
    n.matches("%_init") or
    n.matches("%_exit")
  )
}

/**
 * Heuristic: the function appears to take or hold a sleeping lock,
 * which proves it is not in atomic context.  Used as an additional
 * positive signal (not required).
 */
predicate callsSleepingPrimitive(Function f) {
  exists(FunctionCall fc | fc.getEnclosingFunction() = f |
    fc.getTarget().getName() in [
      "msleep", "msleep_interruptible", "usleep_range", "fsleep",
      "schedule", "schedule_timeout", "schedule_timeout_uninterruptible",
      "mutex_lock", "mutex_lock_interruptible",
      "wait_for_completion", "wait_event_interruptible",
      "down", "down_interruptible"
    ]
  )
}

/**
 * Negative filter: the function (or an obvious caller indicator) suggests
 * atomic context — e.g. IRQ handlers, tasklets, timers, spin-lock holders.
 */
predicate looksAtomic(Function f) {
  exists(string n | n = f.getName() |
    n.matches("%_isr") or
    n.matches("%_irq") or
    n.matches("%_irq_handler") or
    n.matches("%_interrupt") or
    n.matches("%_tasklet") or
    n.matches("%_timer") or
    n.matches("%_nmi") or
    n.matches("%_poll")
  )
  or
  exists(FunctionCall fc | fc.getEnclosingFunction() = f |
    fc.getTarget().getName() in [
      "spin_lock", "spin_lock_irq", "spin_lock_irqsave", "spin_lock_bh",
      "raw_spin_lock", "raw_spin_lock_irq", "raw_spin_lock_irqsave",
      "local_irq_disable", "local_irq_save", "preempt_disable",
      "rcu_read_lock", "rcu_read_lock_bh", "rcu_read_lock_sched"
    ]
  )
}

from BusyDelayCall call, Function f
where
  f = call.getEnclosingFunction() and
  isSleepableContextFunction(f) and
  not looksAtomic(f) and
  // Only flag delays long enough that sleeping is clearly preferable
  // (>= 1 ms equivalent).  Unknown/non-constant delays are also flagged.
  (
    not exists(call.getDelayUsec()) or
    call.getDelayUsec() >= 1000
  )
select call,
  "Busy-wait " + call.getTarget().getName() +
    "() in process-context function '" + f.getName() +
    "'; consider replacing with msleep()/usleep_range()/fsleep() to yield the CPU."
