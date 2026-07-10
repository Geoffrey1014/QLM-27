/**
 * @name Busy-wait delay in non-atomic (sleepable) context
 * @description Calls to busy-waiting delay primitives such as mdelay()/udelay()/ndelay()
 *              from a sleepable context (e.g. workqueue handlers, ioctl/read/write file
 *              ops, probe/remove, kthread bodies) waste CPU cycles. In such contexts the
 *              code should use a sleeping delay (usleep_range, msleep, fsleep) instead.
 *              The pattern is the converse of the more famous sleep-in-atomic bug: here
 *              we busy-wait in a place where it is safe (and preferable) to sleep.
 * @kind problem
 * @problem.severity warning
 * @id cpp/busy-wait-in-sleepable-context
 * @tags performance
 *       correctness
 */

import cpp
import semmle.code.cpp.controlflow.IRGuards

/**
 * A busy-waiting delay routine that spins instead of sleeping.
 * Family: mdelay/udelay/ndelay and their __ variants.
 */
class BusyWaitDelayCall extends FunctionCall {
  BusyWaitDelayCall() {
    exists(string n | n = this.getTarget().getName() |
      n = "mdelay" or
      n = "udelay" or
      n = "ndelay" or
      n = "__mdelay" or
      n = "__udelay" or
      n = "__ndelay" or
      n = "__const_udelay" or
      n = "__delay"
    )
  }
}

/**
 * A function whose body is allowed to sleep (process context, never atomic).
 * Heuristics — match by callback "shape" rather than a single name:
 *   - workqueue / delayed-work handlers: `void f(struct work_struct *)`
 *   - kthread bodies: `int f(void *)` registered via kthread_run/kthread_create
 *   - file_operations callbacks (read/write/ioctl/open/release/mmap/...)
 *   - driver probe()/remove() (struct *_driver members)
 * Recognising the exact registration site is hard in CodeQL without taint, so we
 * approximate by the signature + name suffix conventions that are extremely
 * stable across the kernel.
 */
class SleepableFunction extends Function {
  SleepableFunction() {
    // workqueue handler:  void name(struct work_struct *)
    (
      this.getType() instanceof VoidType and
      this.getNumberOfParameters() = 1 and
      exists(PointerType pt, Type pointee |
        pt = this.getParameter(0).getType() and
        pointee = pt.getBaseType() and
        pointee.getName() = "work_struct"
      )
    )
    or
    // Function ends in _work / _handler / _worker / _fn typical of work callbacks
    this.getName().regexpMatch(".*(_work|_worker|_dwork|_handler_work)$") and
    this.getType() instanceof VoidType
    or
    // file_operations / driver callbacks by conventional name suffix
    this.getName().regexpMatch(
      ".*(_probe|_remove|_open|_release|_ioctl|_unlocked_ioctl|_compat_ioctl|" +
      "_read|_write|_mmap|_show|_store|_thread|_kthread|_poll|_fsync|_flush)$"
    )
    or
    // kthread function:  int name(void *)
    (
      this.getType().getName() = "int" and
      this.getNumberOfParameters() = 1 and
      exists(PointerType pt |
        pt = this.getParameter(0).getType() and
        pt.getBaseType() instanceof VoidType
      ) and
      this.getName().regexpMatch(".*(thread|kthread).*")
    )
  }
}

/**
 * A function that itself looks atomic-context-only: irq/softirq/tasklet/timer
 * handlers or anything called with a spinlock held. We exclude these from being
 * "sleepable" via name conventions to keep false positives down.
 */
class ProbablyAtomicFunction extends Function {
  ProbablyAtomicFunction() {
    this.getName().regexpMatch(
      ".*(_irq|_isr|_interrupt|_irqhandler|_tasklet|_timer|_softirq|" +
      "_nmi|_panic|_reset)$"
    )
  }
}

/**
 * Heuristic: does `caller` (transitively, depth ≤ 2) take a spinlock before
 * `call`?  We use this as an additional FP filter — if any lock-acquire appears
 * earlier in the same function, we skip.
 */
predicate spinLockHeldBefore(FunctionCall call) {
  exists(FunctionCall lk |
    lk.getEnclosingFunction() = call.getEnclosingFunction() and
    lk.getTarget()
        .getName()
        .regexpMatch(
          "spin_lock|spin_lock_irq|spin_lock_irqsave|spin_lock_bh|" +
          "raw_spin_lock|raw_spin_lock_irq|raw_spin_lock_irqsave|" +
          "read_lock|write_lock|local_irq_save|local_irq_disable|" +
          "preempt_disable|rcu_read_lock"
        ) and
    lk.getLocation().getStartLine() < call.getLocation().getStartLine()
  )
}

from BusyWaitDelayCall call, SleepableFunction f, int us
where
  call.getEnclosingFunction() = f and
  not f instanceof ProbablyAtomicFunction and
  not spinLockHeldBefore(call) and
  // Only flag delays long enough that sleeping is clearly preferable.
  // mdelay(x)  -> x*1000 us;  udelay(x) -> x us;  ndelay -> x/1000 us.
  exists(Expr arg | arg = call.getArgument(0) |
    if call.getTarget().getName().matches("%mdelay")
    then us = arg.getValue().toInt() * 1000
    else
      if call.getTarget().getName().matches("%udelay")
      then us = arg.getValue().toInt()
      else
        if call.getTarget().getName().matches("%ndelay")
        then us = arg.getValue().toInt() / 1000
        else us = 0
  ) and
  us >= 10
select call,
  "Busy-wait $@ (~" + us.toString() +
    " us) in sleepable function '" + f.getName() +
    "'; consider usleep_range()/msleep() to avoid wasting CPU.",
  call, call.getTarget().getName()
