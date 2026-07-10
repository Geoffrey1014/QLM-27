/**
 * @name Busy-wait mdelay() in a sleepable (non-atomic) context
 * @description Flags calls to `mdelay()` made inside functions that
 *              execute in a process / sleepable context (probe, init,
 *              resume, suspend, remove, open, release, write, read,
 *              ioctl, work / workfn handlers, threads, mount, etc.).
 *              In such contexts the kernel allows yielding, so the
 *              busy-wait mdelay() should be replaced with the sleeping
 *              usleep_range() / msleep() to free the CPU. mdelay() is
 *              only correct in true atomic contexts (IRQ handler /
 *              spinlock held / preempt disabled). Pattern source:
 *              DCNS (Bai et al.).
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-dgfp-5
 */

import cpp

/**
 * Names of "sleeping" delay / wait primitives — proxies for
 * "this function is allowed to sleep". Used to compute a per-function
 * may-sleep evidence signal without crossing call boundaries (the
 * cell spec requires a monolithic query).
 */
predicate isSleepingPrimitive(string name) {
  name = "msleep" or
  name = "msleep_interruptible" or
  name = "usleep_range" or
  name = "usleep_range_state" or
  name = "ssleep" or
  name = "schedule" or
  name = "schedule_timeout" or
  name = "schedule_timeout_interruptible" or
  name = "schedule_timeout_uninterruptible" or
  name = "wait_event" or
  name = "wait_event_interruptible" or
  name = "wait_event_timeout" or
  name = "mutex_lock" or
  name = "mutex_lock_interruptible" or
  name = "down" or
  name = "down_interruptible"
}

/**
 * Function names that conventionally run in process / sleepable
 * context in the Linux kernel. Suffix / substring heuristic over
 * the function's own name (covers both bare entry points like
 * `probe` and wrapper names like `pci_epf_test_write`).
 */
bindingset[n]
predicate sleepableFunctionName(string n) {
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
  n.matches("%_handler%") or
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

from FunctionCall call, Function fn, string msg
where
  call.getTarget().getName() = "mdelay" and
  fn = call.getEnclosingFunction() and
  inSleepableContext(fn) and
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
        "'; replace with usleep_range()/msleep() to yield CPU."
select call, msg
