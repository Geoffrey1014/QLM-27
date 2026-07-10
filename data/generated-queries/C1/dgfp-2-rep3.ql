/**
 * @name Busy-wait mdelay() in a sleepable (non-atomic) context
 * @description Flags calls to `mdelay()` made inside functions that
 *              execute in a process / sleepable context (probe,
 *              remove, init, exit, suspend, resume, open, release,
 *              ioctl, read, write, thread, work handlers, mount,
 *              fill_super), where `msleep()` should be used instead
 *              to yield the CPU. mdelay() busy-waits and wastes CPU
 *              cycles on long delays; only correct in true atomic
 *              context (IRQ handler / spinlock held / preempt
 *              disabled). Pattern source: DCNS (Bai et al.).
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-dgfp-2
 */

import cpp

/**
 * Names of "sleeping" delay primitives — proxies for "this function
 * is allowed to sleep". We use these to compute a per-function
 * may-sleep evidence signal without crossing call boundaries (the
 * cell spec requires a monolithic query).
 */
predicate isSleepingPrimitive(string name) {
  name = "msleep" or
  name = "msleep_interruptible" or
  name = "usleep_range" or
  name = "usleep_range_state" or
  name = "ssleep" or
  name = "schedule_timeout" or
  name = "schedule_timeout_interruptible" or
  name = "schedule_timeout_uninterruptible" or
  name = "wait_event" or
  name = "wait_event_interruptible" or
  name = "wait_event_timeout" or
  name = "mutex_lock" or
  name = "mutex_lock_interruptible" or
  name = "down" or
  name = "down_interruptible" or
  name = "kmalloc" or
  name = "kzalloc" or
  name = "kcalloc"
}

/**
 * Function-name suffixes that conventionally run in process /
 * sleepable context in the Linux kernel.
 */
predicate sleepableSuffix(string suf) {
  suf = "_resume" or suf = "_suspend" or suf = "_probe" or
  suf = "_remove" or suf = "_open" or suf = "_release" or
  suf = "_init" or suf = "_exit" or suf = "_thread" or
  suf = "_work" or suf = "_workfn" or suf = "_ioctl" or
  suf = "_read" or suf = "_write" or suf = "_mount" or
  suf = "_fill_super" or suf = "_show" or suf = "_store"
}

predicate sleepableBareName(string n) {
  n = "probe" or n = "remove" or n = "open" or n = "release" or
  n = "resume" or n = "suspend" or n = "ioctl" or
  n = "read" or n = "write"
}

/**
 * Either (a) the enclosing function's name fits a sleepable
 * convention, or (b) it independently calls a sleeping primitive.
 * Either is accepted; both compound on the full kernel DB.
 */
predicate inSleepableContext(Function f) {
  sleepableBareName(f.getName())
  or
  exists(string suf |
    sleepableSuffix(suf) and
    (f.getName().matches("%" + suf) or f.getName().matches("%" + suf + "_%"))
  )
  or
  exists(FunctionCall sc |
    sc.getEnclosingFunction() = f and
    isSleepingPrimitive(sc.getTarget().getName())
  )
}

/**
 * Constant millisecond argument >= 10 — empirical "long enough to
 * be wrong to busy-wait" cutoff (DCNS / DSAC). Non-constant args are
 * also flagged since they are unbounded.
 */
predicate longDelayArg(Expr arg) {
  not exists(arg.getValue())
  or
  arg.getValue().toInt() >= 10
}

from FunctionCall call, Function fn, string msg
where
  call.getTarget().getName() = "mdelay" and
  fn = call.getEnclosingFunction() and
  inSleepableContext(fn) and
  longDelayArg(call.getArgument(0)) and
  // Exclude obvious atomic-context callers: any spin_lock_* /
  // local_irq_disable / preempt_disable appearing in the same
  // function before the mdelay call.
  not exists(FunctionCall atomic |
    atomic.getEnclosingFunction() = fn and
    (
      atomic.getTarget().getName().matches("spin_lock%") or
      atomic.getTarget().getName().matches("raw_spin_lock%") or
      atomic.getTarget().getName() = "local_irq_disable" or
      atomic.getTarget().getName() = "local_irq_save" or
      atomic.getTarget().getName() = "preempt_disable" or
      atomic.getTarget().getName() = "rcu_read_lock"
    ) and
    atomic.getLocation().getStartLine() < call.getLocation().getStartLine()
  ) and
  msg = "mdelay() called inside sleepable function '" + fn.getName() +
        "'; replace with msleep() to yield CPU."
select call, msg
