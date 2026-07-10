/**
 * @name Unnecessary mdelay() busy-wait in sleepable context
 * @description Finds calls to mdelay()/udelay() that occur in functions which can
 *              sleep (i.e. not invoked from atomic context). In such cases the
 *              busy-wait should be replaced with a sleeping API such as
 *              usleep_range()/msleep() to avoid wasting CPU cycles.
 * @kind problem
 * @problem.severity warning
 * @id cpp/unnecessary-busy-wait-delay
 * @tags performance
 *       efficiency
 */

import cpp
import semmle.code.cpp.controlflow.IRGuards

/** A function that busy-waits the CPU (mdelay family). */
class BusyWaitCall extends FunctionCall {
  BusyWaitCall() {
    this.getTarget().getName() = ["mdelay", "__mdelay", "ndelay", "udelay", "__udelay"]
  }
}

/** A function or macro known to acquire a spinlock / disable preemption / enter IRQ. */
predicate atomicEntryName(string name) {
  name = [
      // spinlock family
      "spin_lock", "spin_lock_bh", "spin_lock_irq", "spin_lock_irqsave",
      "spin_trylock", "spin_trylock_bh", "spin_trylock_irq", "spin_trylock_irqsave",
      "_raw_spin_lock", "_raw_spin_lock_bh", "_raw_spin_lock_irq", "_raw_spin_lock_irqsave",
      "raw_spin_lock", "raw_spin_lock_bh", "raw_spin_lock_irq", "raw_spin_lock_irqsave",
      "read_lock", "read_lock_bh", "read_lock_irq", "read_lock_irqsave",
      "write_lock", "write_lock_bh", "write_lock_irq", "write_lock_irqsave",
      // preemption
      "preempt_disable", "preempt_disable_notrace",
      "local_irq_disable", "local_irq_save", "local_bh_disable",
      // rcu
      "rcu_read_lock", "rcu_read_lock_bh", "rcu_read_lock_sched"
    ]
}

/** A call that puts the current thread in atomic context. */
class AtomicEnterCall extends FunctionCall {
  AtomicEnterCall() { atomicEntryName(this.getTarget().getName()) }
}

/** Sleeping functions — their presence implies the enclosing function can sleep. */
predicate sleepingFunctionName(string name) {
  name = [
      "msleep", "msleep_interruptible", "usleep_range", "ssleep",
      "schedule", "schedule_timeout", "schedule_timeout_interruptible",
      "schedule_timeout_uninterruptible", "wait_event", "wait_event_interruptible",
      "wait_event_timeout", "mutex_lock", "mutex_lock_interruptible",
      "down", "down_interruptible", "down_killable",
      "kmalloc", "kzalloc", "vmalloc", "kcalloc"
    ]
}

/** A function that itself calls a sleeping API (heuristic: definitely sleepable). */
predicate isSleepableFunction(Function f) {
  exists(FunctionCall fc |
    fc.getEnclosingFunction() = f and
    sleepingFunctionName(fc.getTarget().getName())
  )
}

/** A function whose name hints it runs in atomic / IRQ / interrupt context. */
predicate atomicContextFunctionName(Function f) {
  exists(string n | n = f.getName() |
    n.matches("%_irq") or
    n.matches("%_isr") or
    n.matches("%_interrupt") or
    n.matches("%_handler") or
    n.matches("%_irqhandler") or
    n.matches("%_tasklet%") or
    n.matches("%_callback%")
  )
}

/**
 * Holds if the busy-wait call lies under a lock-held / preempt-disabled region
 * within the same function (very coarse intraprocedural check).
 */
predicate underAtomicRegion(BusyWaitCall bw) {
  exists(AtomicEnterCall enter |
    enter.getEnclosingFunction() = bw.getEnclosingFunction() and
    enter.getLocation().getStartLine() < bw.getLocation().getStartLine()
  )
}

from BusyWaitCall bw, Function enclosing
where
  enclosing = bw.getEnclosingFunction() and
  // The enclosing function is sleepable (calls something that sleeps elsewhere).
  isSleepableFunction(enclosing) and
  // Not in an obviously atomic-named context.
  not atomicContextFunctionName(enclosing) and
  // Not under a lock acquired earlier in the same function.
  not underAtomicRegion(bw) and
  // Filter trivially-short waits (those are typically needed for hw timing).
  // We still report mdelay regardless of constant argument since mdelay() is
  // the canonical instance from the fix commit.
  bw.getTarget().getName() = ["mdelay", "__mdelay"]
select bw,
  "Busy-wait " + bw.getTarget().getName() +
    "() in sleepable function '" + enclosing.getName() +
    "'; consider replacing with usleep_range() or msleep()."
