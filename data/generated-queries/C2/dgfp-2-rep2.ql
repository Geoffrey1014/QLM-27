/**
 * @name  rq3-c2-dgfp-2-rep2
 * @id    cpp/rq3/c2/dgfp-2-rep2
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects mdelay() busy-wait calls in sleepable contexts where
 *              msleep() should be used instead. Seed: cavium cpt cpt_device_init
 *              replaced mdelay(100) with msleep(100).
 */

import cpp

/** Holds if `fc` is a direct call to the busy-wait API `mdelay`. */
predicate isMdelayCall(FunctionCall fc) {
  fc.getTarget().getName() = "mdelay"
}

/**
 * Holds if `fc` is an `mdelay` call whose argument is a compile-time constant
 * of at least 10 ms. Below ~10 ms `msleep` is not a faithful replacement
 * (scheduler granularity), so we exclude shorter delays to keep precision.
 */
predicate isLongMdelay(FunctionCall fc) {
  isMdelayCall(fc) and
  exists(Expr arg | arg = fc.getArgument(0) |
    arg.getValue().toInt() >= 10
  )
}

/**
 * Holds if `f` looks like a function that runs in a sleepable (non-atomic)
 * context: probe/init/remove/shutdown PCI/platform callbacks, suspend/resume,
 * file-ops open/release, or workqueue handlers.
 */
predicate isSleepableContextFunction(Function f) {
  exists(string n | n = f.getName() |
    n.matches("%_probe") or
    n.matches("%_init") or
    n = "init" or n = "probe" or
    n.matches("%_remove") or
    n.matches("%_shutdown") or
    n.matches("%_suspend") or
    n.matches("%_resume") or
    n.matches("%_open") or
    n.matches("%_release") or
    n.matches("%_work") or
    n.matches("%_work_fn") or
    n.matches("%_workfn") or
    n.matches("%_thread")
  )
}

/**
 * Holds if `f` is plausibly an atomic-context function we should NOT flag:
 * interrupt handlers, tasklets, timer callbacks. Used to suppress false
 * positives where the name pattern overlaps with sleepable conventions.
 */
predicate isAtomicContextFunction(Function f) {
  exists(string n | n = f.getName() |
    n.matches("%_isr") or
    n.matches("%_irq") or
    n.matches("%_irq_handler") or
    n.matches("%_interrupt") or
    n.matches("%_tasklet") or
    n.matches("%_timer") or
    n.matches("%_callback")
  )
}

/**
 * Holds if `fc` is a long `mdelay` call whose enclosing function `f` looks
 * sleepable and is not flagged as atomic.
 */
predicate mdelayInSleepableContext(FunctionCall fc, Function f) {
  isLongMdelay(fc) and
  fc.getEnclosingFunction() = f and
  isSleepableContextFunction(f) and
  not isAtomicContextFunction(f)
}

from FunctionCall fc, Function f
where mdelayInSleepableContext(fc, f)
select fc,
  "mdelay() called in sleepable context function '" + f.getName() +
  "'; consider replacing with msleep() to avoid busy-waiting."
