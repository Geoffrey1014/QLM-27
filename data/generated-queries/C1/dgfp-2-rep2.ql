/**
 * @name Busy-wait mdelay() in a sleepable (non-atomic) context
 * @description Flags calls to `mdelay()` made inside functions that
 *              execute in a process / sleepable context (probe, init,
 *              resume, suspend, remove, open, release, exit, thread,
 *              work handlers, ioctl, read, write, mount, fill_super),
 *              where `msleep()` should be used instead to yield the
 *              CPU. mdelay() busy-waits and wastes CPU cycles on long
 *              delays; only correct in true atomic context (IRQ
 *              handler / spinlock held / preempt disabled). Pattern
 *              source: DCNS (Bai et al.).
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-dgfp-2
 */

import cpp

/**
 * Names of "sleeping" delay primitives — proxies for "this function
 * is allowed to sleep". Used to compute a per-function may-sleep
 * evidence signal without crossing call boundaries (the cell spec
 * requires a monolithic query).
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
 * Function names that conventionally run in process / sleepable
 * context in the Linux kernel. Suffix-based heuristic.
 */
bindingset[n]
predicate sleepableFunctionName(string n) {
  // Use contains-style matching so the predicate also tolerates the
  // common suffix patterns that wrap entry-point names (e.g. test
  // doubles, instrumented variants). The underscore-delimited stems
  // are characteristic of kernel-style entry points that always run
  // in process / sleepable context.
  n.matches("%_resume%") or
  n.matches("%_suspend%") or
  n.matches("%_probe%") or
  n.matches("%_remove%") or
  n.matches("%_open%") or
  n.matches("%_release%") or
  n.matches("%_init%") or
  n.matches("%_exit%") or
  n.matches("%_thread%") or
  n.matches("%_work%") or
  n.matches("%_workfn%") or
  n.matches("%_ioctl%") or
  n.matches("%_read%") or
  n.matches("%_write%") or
  n.matches("%_mount%") or
  n.matches("%_fill_super%") or
  n.matches("%_show%") or
  n.matches("%_store%") or
  n.matches("%_device_init%") or
  n = "probe" or n = "remove" or n = "open" or n = "release" or
  n = "resume" or n = "suspend" or n = "ioctl" or
  n = "read" or n = "write"
}

/**
 * True if the enclosing function (a) has a "sleepable" entry-point-style
 * name OR (b) calls something else known to be a sleeping primitive.
 */
predicate inSleepableContext(Function f) {
  exists(string n | n = f.getName() | sleepableFunctionName(n))
  or
  exists(FunctionCall sc |
    sc.getEnclosingFunction() = f and
    isSleepingPrimitive(sc.getTarget().getName())
  )
}

/**
 * A constant millisecond argument >= 10 is the empirical cutoff for
 * "long enough that busy-waiting is wrong" (DCNS / DSAC threshold).
 * Non-constant args are also flagged — they're unbounded.
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
