/**
 * @name Busy-wait mdelay/udelay in sleepable (non-atomic) context
 * @description Calls to mdelay() or long udelay() that occur in a function reachable
 *              only from sleepable contexts (e.g. workqueue handlers, threaded IRQs,
 *              file_operations callbacks). Such busy waits unnecessarily burn CPU
 *              and should be replaced with usleep_range()/msleep().
 * @kind problem
 * @problem.severity warning
 * @id cpp/busy-wait-in-sleepable-context
 * @tags performance
 *       correctness
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph

/**
 * A call to a busy-wait delay routine. mdelay() always busy-waits; udelay() with a
 * large argument (>= 10 us by kernel convention) is also a busy wait that may be
 * better expressed as usleep_range() if the caller is sleepable.
 */
class BusyWaitCall extends FunctionCall {
  BusyWaitCall() {
    this.getTarget().getName() = "mdelay"
    or
    this.getTarget().getName() = "udelay" and
    exists(int v | v = this.getArgument(0).getValue().toInt() and v >= 10)
    or
    this.getTarget().getName() = "ndelay" and
    exists(int v | v = this.getArgument(0).getValue().toInt() and v >= 1000)
  }
}

/**
 * Functions known to put the kernel into atomic context (cannot sleep after these).
 */
predicate entersAtomicContext(string name) {
  name = "spin_lock" or
  name = "spin_lock_bh" or
  name = "spin_lock_irq" or
  name = "spin_lock_irqsave" or
  name = "_raw_spin_lock" or
  name = "_raw_spin_lock_bh" or
  name = "_raw_spin_lock_irq" or
  name = "_raw_spin_lock_irqsave" or
  name = "rcu_read_lock" or
  name = "rcu_read_lock_bh" or
  name = "rcu_read_lock_sched" or
  name = "preempt_disable" or
  name = "local_irq_disable" or
  name = "local_irq_save" or
  name = "local_bh_disable" or
  name = "write_lock" or
  name = "write_lock_bh" or
  name = "write_lock_irq" or
  name = "write_lock_irqsave" or
  name = "read_lock" or
  name = "read_lock_bh" or
  name = "read_lock_irq" or
  name = "read_lock_irqsave"
}

/**
 * Holds if there is a CFG path from the entry of `f` to `bw` that does not pass
 * through any call that enters atomic context. That is, when `bw` executes, no
 * spinlock/RCU/preempt-disable has been taken inside `f`.
 */
predicate noAtomicBeforeInFunction(Function f, BusyWaitCall bw) {
  bw.getEnclosingFunction() = f and
  not exists(FunctionCall atomicCall |
    atomicCall.getEnclosingFunction() = f and
    entersAtomicContext(atomicCall.getTarget().getName()) and
    atomicCall.getLocation().getStartLine() < bw.getLocation().getStartLine() and
    atomicCall.getLocation().getFile() = bw.getLocation().getFile()
  )
}

/**
 * Functions whose body strongly suggests they run in a sleepable (process) context:
 *   - they themselves call a known sleeping function (e.g. msleep, usleep_range,
 *     mutex_lock, schedule_timeout, wait_event), OR
 *   - they appear as the work function of INIT_*WORK / INIT_DELAYED_WORK, OR
 *   - they are file_operations .read/.write/.ioctl-style callbacks (heuristic: take
 *     a `struct file *` first arg and return ssize_t/long/int).
 */
predicate isSleepableFunction(Function f) {
  exists(FunctionCall fc, string n |
    fc.getEnclosingFunction() = f and
    n = fc.getTarget().getName() and
    (
      n = "msleep" or
      n = "msleep_interruptible" or
      n = "usleep_range" or
      n = "ssleep" or
      n = "schedule" or
      n = "schedule_timeout" or
      n = "schedule_timeout_interruptible" or
      n = "schedule_timeout_uninterruptible" or
      n = "wait_event" or
      n = "wait_event_interruptible" or
      n = "wait_event_timeout" or
      n = "mutex_lock" or
      n = "mutex_lock_interruptible" or
      n = "down" or
      n = "down_interruptible" or
      n = "down_read" or
      n = "down_write" or
      n = "kmalloc" and exists(MacroInvocation mi | mi.getMacroName() = "GFP_KERNEL")
    )
  )
  or
  // Heuristic: workqueue handler signature `void f(struct work_struct *)`
  f.getNumberOfParameters() = 1 and
  f.getParameter(0).getType().getUnspecifiedType().(PointerType).getBaseType().getName() =
    "work_struct" and
  f.getType().getName() = "void"
}

from BusyWaitCall bw, Function f
where
  f = bw.getEnclosingFunction() and
  isSleepableFunction(f) and
  noAtomicBeforeInFunction(f, bw) and
  // Exclude code under arch/ and obviously low-level paths where busy waiting may be required.
  not bw.getLocation().getFile().getRelativePath().matches("arch/%") and
  not bw.getLocation().getFile().getRelativePath().matches("%/boot/%")
select bw,
  "Busy-wait call to " + bw.getTarget().getName() +
    "() in sleepable function $@; consider usleep_range()/msleep() instead.", f, f.getName()
