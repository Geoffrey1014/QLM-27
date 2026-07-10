/**
 * @name  rq3-c2-dgfp-1-rep1
 * @id    cpp/rq3/c2/dgfp-1-rep1
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects mdelay() busy-wait calls in sleepable contexts where
 *              msleep() should be used instead.
 */

import cpp

/** Holds if `fc` is a direct call to the busy-wait API `mdelay`. */
predicate isMdelayCall(FunctionCall fc) {
  fc.getTarget().getName() = "mdelay"
}

/**
 * Holds if `f` looks like a function that runs in a sleepable (non-atomic)
 * context: PM suspend/resume callbacks, probe, remove, shutdown, open/release
 * file-ops, or workqueue handlers. These are commonly invoked by the kernel
 * without holding any spinlock.
 */
predicate isSleepableContextFunction(Function f) {
  exists(string n | n = f.getName() |
    n.matches("%_resume") or
    n.matches("%_suspend") or
    n.matches("%_probe") or
    n.matches("%_remove") or
    n.matches("%_shutdown") or
    n.matches("%_open") or
    n.matches("%_release") or
    n.matches("%_work") or
    n = "resume" or n = "suspend" or n = "probe"
  )
}

/**
 * Holds if `f` is plausibly an atomic-context function: interrupt handler,
 * timer callback, tasklet, or anything ending in `_irq` / `_isr` /
 * `_handler` / `_callback` that's typically invoked with IRQs disabled.
 */
predicate isAtomicContextFunction(Function f) {
  exists(string n | n = f.getName() |
    n.matches("%_isr") or
    n.matches("%_irq_handler") or
    n.matches("%_interrupt") or
    n.matches("%_tasklet") or
    n.matches("%_timer")
  )
}

/**
 * Holds if `fc` is an `mdelay` call located inside a function `f` that is
 * plausibly running in a sleepable context (and is not an atomic-context
 * handler).
 */
predicate callsMdelayInSleepableContext(FunctionCall fc, Function f) {
  isMdelayCall(fc) and
  fc.getEnclosingFunction() = f and
  isSleepableContextFunction(f) and
  not isAtomicContextFunction(f)
}

from FunctionCall fc, Function f
where callsMdelayInSleepableContext(fc, f)
select fc,
  "mdelay() called in sleepable context function '" + f.getName() +
  "'; consider replacing with msleep() to avoid busy-waiting."
