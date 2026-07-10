/**
 * @name Busy-wait mdelay in sleepable context
 * @description Detects calls to busy-wait delay functions like `mdelay()`
 *              that occur in functions that are not invoked in atomic context.
 *              Such calls waste CPU cycles and should be replaced with a
 *              sleeping alternative like `usleep_range()` or `msleep()`.
 *              Heuristic: a function is considered safe to sleep in if it is
 *              not invoked from any IRQ/atomic-looking caller, it acquires no
 *              spinlock locally, and it itself already calls another sleeping
 *              primitive (so we know the surrounding code is sleepable).
 * @kind problem
 * @problem.severity warning
 * @id cpp/busy-wait-mdelay-in-sleepable-context
 * @tags performance
 *       correctness
 */

import cpp

/** A function call to a busy-wait delay primitive. */
class BusyWaitDelayCall extends FunctionCall {
  BusyWaitDelayCall() {
    this.getTarget().getName() = ["mdelay", "udelay", "ndelay", "__udelay", "__ndelay"]
  }
}

/** Names of functions/macros that put a CPU in atomic context. */
predicate atomicContextEntry(string name) {
  name = [
    "spin_lock", "spin_lock_irq", "spin_lock_irqsave", "spin_lock_bh",
    "spin_trylock", "spin_trylock_irq", "spin_trylock_irqsave", "spin_trylock_bh",
    "raw_spin_lock", "raw_spin_lock_irq", "raw_spin_lock_irqsave", "raw_spin_lock_bh",
    "read_lock", "read_lock_irq", "read_lock_irqsave", "read_lock_bh",
    "write_lock", "write_lock_irq", "write_lock_irqsave", "write_lock_bh",
    "rcu_read_lock", "rcu_read_lock_bh", "rcu_read_lock_sched",
    "preempt_disable", "local_bh_disable", "local_irq_disable", "local_irq_save"
  ]
}

/** Names of functions known to sleep / require sleepable context. */
predicate sleepingFunction(string name) {
  name = [
    "msleep", "msleep_interruptible", "ssleep",
    "usleep_range", "usleep_range_state",
    "schedule", "schedule_timeout", "schedule_timeout_interruptible",
    "schedule_timeout_uninterruptible", "schedule_timeout_killable",
    "wait_event", "wait_event_interruptible", "wait_event_timeout",
    "wait_event_interruptible_timeout", "wait_event_killable",
    "mutex_lock", "mutex_lock_interruptible", "mutex_lock_killable",
    "down", "down_interruptible", "down_killable",
    "kmalloc", "kzalloc", "kcalloc", "krealloc", "vmalloc", "vzalloc",
    "fsleep", "cond_resched"
  ]
}

/** The enclosing function holds a spinlock or disables preemption locally. */
predicate hasAtomicEntryLocally(Function f) {
  exists(FunctionCall fc | fc.getEnclosingFunction() = f and atomicContextEntry(fc.getTarget().getName()))
}

/** The enclosing function itself calls a sleeping primitive other than the busy-wait. */
predicate callsSleepingPrimitive(Function f) {
  exists(FunctionCall fc |
    fc.getEnclosingFunction() = f and
    sleepingFunction(fc.getTarget().getName())
  )
}

/**
 * The function's name suggests it might be invoked from atomic context
 * (interrupt handler, tasklet, softirq, atomic callback).
 */
predicate suspectAtomicByName(Function f) {
  exists(string n | n = f.getName() |
    n.matches("%_isr") or n.matches("%_irq") or n.matches("%_irq_handler") or
    n.matches("%_interrupt") or n.matches("%_tasklet") or n.matches("%_softirq") or
    n.matches("irq_%") or n.matches("isr_%")
  )
}

from BusyWaitDelayCall call, Function f
where
  f = call.getEnclosingFunction() and
  // The enclosing function appears to run in sleepable context:
  not hasAtomicEntryLocally(f) and
  not suspectAtomicByName(f) and
  // And we have evidence the surrounding context is sleepable:
  callsSleepingPrimitive(f) and
  // Exclude trivial/short busy waits typically guarded by hardware constraints:
  // we still report mdelay; udelay/ndelay are kept but the pattern is generic.
  not call.getFile().getRelativePath().matches("arch/%")
select call,
  "Busy-wait '" + call.getTarget().getName() +
    "()' in function '" + f.getName() +
    "' which appears to run in sleepable context (calls a sleeping primitive). " +
    "Consider replacing with usleep_range() or msleep()."
