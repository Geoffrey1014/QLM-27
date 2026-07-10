/**
 * @name mdelay used in non-atomic (sleepable) context
 * @description Calls to mdelay()/udelay() with large delays from functions that
 *              run in process / sleepable context busy-wait the CPU unnecessarily.
 *              Such calls should be replaced with msleep()/usleep_range() to
 *              release the CPU. Pattern based on the cpt_device_init mdelay->msleep
 *              fix (commit e9acf05255cb).
 * @kind problem
 * @problem.severity warning
 * @id cpp/kernel-busy-wait-in-sleepable-context
 * @tags correctness
 *       performance
 *       kernel
 */

import cpp
import semmle.code.cpp.controlflow.IRGuards

/**
 * A call to a busy-wait delay function (mdelay or large udelay).
 * mdelay(N) expands to N*1000 udelay; both burn CPU.
 */
class BusyWaitCall extends FunctionCall {
  BusyWaitCall() {
    this.getTarget().getName() = "mdelay"
    or
    // udelay called with a constant >= 1000us (>=1ms) is also a candidate
    this.getTarget().getName() = "udelay" and
    exists(int v |
      v = this.getArgument(0).getValue().toInt() and
      v >= 1000
    )
  }

  /** The delay magnitude in microseconds, when statically known. */
  int getDelayMicros() {
    this.getTarget().getName() = "mdelay" and
    result = this.getArgument(0).getValue().toInt() * 1000
    or
    this.getTarget().getName() = "udelay" and
    result = this.getArgument(0).getValue().toInt()
  }
}

/**
 * Functions known to require atomic / non-sleepable context. If the enclosing
 * function is one of these (or is called from one), we exclude it: mdelay is
 * the right primitive there.
 */
class AtomicEntryFunction extends Function {
  AtomicEntryFunction() {
    // IRQ / softirq / tasklet / timer handlers conventionally end in these
    // suffixes or take these typedef'd parameters.
    exists(Parameter p |
      p = this.getAParameter() and
      p.getType().getName().regexpMatch("(irqreturn_t.*|.*tasklet_struct.*|.*timer_list.*|.*hrtimer.*)")
    )
    or
    this.getName().regexpMatch(".*_(isr|irq_handler|interrupt|tasklet|timer_cb|timer_fn|softirq)")
    or
    this.getName().regexpMatch("(do_|handle_).*_(irq|softirq|nmi)")
  }
}

/**
 * Functions that, by structural evidence, run in process / sleepable context:
 *  - probe / remove / open / release / init callbacks
 *  - explicit calls to known-sleeping APIs (msleep, mutex_lock, wait_event,
 *    schedule, kmalloc(GFP_KERNEL), copy_from_user, ...)
 */
predicate sleepableContextFunction(Function f) {
  // Heuristic 1: name suggests a process-context entry point
  f.getName().regexpMatch(".*(_probe|_remove|_open|_release|_init|_exit|_show|_store|_read|_write|_ioctl|_setup|_configure|_reset_work|_worker)$")
  or
  // Heuristic 2: contains a syscall-like sleeping call
  exists(FunctionCall fc |
    fc.getEnclosingFunction() = f and
    fc.getTarget().getName() in [
      "msleep", "msleep_interruptible", "ssleep",
      "usleep_range", "schedule", "schedule_timeout",
      "mutex_lock", "mutex_lock_interruptible", "down", "down_interruptible",
      "wait_event", "wait_event_interruptible", "wait_event_timeout",
      "copy_from_user", "copy_to_user",
      "kmalloc", "kzalloc", "kcalloc", "vmalloc", "vzalloc"
    ]
  )
}

/**
 * The enclosing function is not known to be atomic, and is known to be sleepable.
 */
predicate inSleepableFunction(BusyWaitCall c) {
  exists(Function f |
    f = c.getEnclosingFunction() and
    sleepableContextFunction(f) and
    not f instanceof AtomicEntryFunction
  )
}

/**
 * Exclude calls that are clearly under spinlock / irq-disable / preempt-disable
 * guards in the same function (best-effort).
 */
predicate underAtomicGuard(BusyWaitCall c) {
  exists(FunctionCall guard, ControlFlowNode acquire |
    guard.getTarget().getName() in [
      "spin_lock", "spin_lock_bh", "spin_lock_irq", "spin_lock_irqsave",
      "raw_spin_lock", "raw_spin_lock_irq", "raw_spin_lock_irqsave",
      "read_lock", "write_lock", "read_lock_irq", "write_lock_irq",
      "local_irq_disable", "local_irq_save",
      "preempt_disable", "rcu_read_lock", "rcu_read_lock_bh"
    ] and
    guard.getEnclosingFunction() = c.getEnclosingFunction() and
    acquire = guard and
    acquire.getASuccessor*() = c
  )
}

from BusyWaitCall c, Function f
where
  f = c.getEnclosingFunction() and
  inSleepableFunction(c) and
  not underAtomicGuard(c) and
  // require a "long" busy-wait: >= 1ms total
  c.getDelayMicros() >= 1000
select c,
  "Busy-wait " + c.getTarget().getName() + "(" + c.getDelayMicros().toString() +
    "us) in sleepable function '" + f.getName() +
    "'; consider replacing with msleep()/usleep_range() to avoid burning the CPU."
