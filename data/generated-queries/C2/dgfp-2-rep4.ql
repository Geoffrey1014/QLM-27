/**
 * @name  rq3-c2-dgfp-2-rep4
 * @id    cpp/rq3/c2/dgfp-2-rep4
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detect mdelay/udelay (busy-wait) calls in sleepable context
 *              that could be replaced with msleep/usleep_range.
 */

import cpp

/** Holds if `fc` is a call to a busy-wait delay function (mdelay/udelay/ndelay). */
predicate isBusyWaitCall(FunctionCall fc) {
  exists(Function callee | callee = fc.getTarget() |
    callee.getName() = "mdelay" or
    callee.getName() = "udelay" or
    callee.getName() = "ndelay" or
    callee.getName() = "__const_udelay" or
    callee.getName() = "__udelay"
  )
}

/**
 * Holds if function `f` looks like it may run in atomic context based on
 * naming heuristics: interrupt handlers, atomic-suffixed helpers, callbacks
 * that the kernel invokes with locks held, or anything containing "irq",
 * "isr", "atomic", "_cb", "tasklet", "softirq" in the name.
 */
predicate isAtomicLikeFunction(Function f) {
  exists(string n | n = f.getName().toLowerCase() |
    n.matches("%_irq%") or
    n.matches("%_isr%") or
    n.matches("%_atomic%") or
    n.matches("%irqhandler%") or
    n.matches("%interrupt%") or
    n.matches("%tasklet%") or
    n.matches("%softirq%") or
    n.matches("%_handler") or
    n.matches("%timer_fn%") or
    n.matches("%_callback") or
    n.matches("%_cb")
  )
}

/**
 * Holds if function `f` looks like it runs in process/sleepable context based
 * on naming heuristics: probe/init/exit/open/release/ioctl/show/store hooks.
 */
predicate isSleepableLikeFunction(Function f) {
  exists(string n | n = f.getName().toLowerCase() |
    n.matches("%_probe") or
    n.matches("%_init") or
    n = "init" or
    n.matches("%_exit") or
    n.matches("%_open") or
    n.matches("%_release") or
    n.matches("%_remove") or
    n.matches("%_ioctl") or
    n.matches("%_show") or
    n.matches("%_store") or
    n.matches("%_setup") or
    n.matches("%_device_init") or
    n.matches("%_hw_init")
  )
}

/**
 * Holds if `fc` is a busy-wait call located in a function whose name
 * suggests sleepable context AND not in a function whose name suggests
 * atomic context.
 */
predicate busyWaitInSleepableContext(FunctionCall fc) {
  isBusyWaitCall(fc) and
  exists(Function enclosing | enclosing = fc.getEnclosingFunction() |
    isSleepableLikeFunction(enclosing) and
    not isAtomicLikeFunction(enclosing)
  )
}

from FunctionCall fc, Function enclosing
where
  busyWaitInSleepableContext(fc) and
  enclosing = fc.getEnclosingFunction()
select fc,
  "Busy-wait call '" + fc.getTarget().getName() +
    "' in sleepable-context function '" + enclosing.getName() +
    "' should likely be replaced with msleep/usleep_range."
