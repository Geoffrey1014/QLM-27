/**
 * @name  rq3-c3-dgfp-2-rep2
 * @id    cpp/rq3/c3/dgfp-2-rep2
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-ON generation for RQ3 cell C3.
 *              Detects mdelay() busy-wait calls of >= 10 ms inside
 *              functions whose name pattern suggests a sleepable
 *              (non-atomic) context (probe/init/remove/shutdown/
 *              suspend/resume/open/release/work/thread), excluding
 *              functions whose name pattern marks them as atomic
 *              (isr/irq/interrupt/tasklet/timer/callback).
 *              Seed: cavium cpt cpt_device_init replaced mdelay(100)
 *              with msleep(100) (commit e9acf05255cb).
 */

import cpp

/** Holds if `fc` is a direct call to the busy-wait API `mdelay`. */
predicate isMdelayCall(FunctionCall fc) {
  fc.getTarget().getName() = "mdelay"
}

/**
 * Holds if `fc` is an `mdelay` call whose argument is a compile-time
 * constant of at least 10 ms. Below ~10 ms `msleep` is not a faithful
 * replacement (scheduler granularity), so we exclude shorter delays.
 */
predicate isLongMdelay(FunctionCall fc) {
  isMdelayCall(fc) and
  exists(Expr arg | arg = fc.getArgument(0) |
    arg.getValue().toInt() >= 10
  )
}

/**
 * Holds if `f` looks like a function that runs in a sleepable
 * (non-atomic) context: PCI/platform probe/init/remove/shutdown,
 * suspend/resume, file-ops open/release, workqueue handlers, kernel
 * threads. Uses substring patterns so POC-style suffixes such as
 * `_init_buggy` still match.
 */
predicate isSleepableContextFunction(Function f) {
  exists(string n | n = f.getName() |
    n.matches("%_probe%") or
    n.matches("%_init%") or
    n = "init" or n = "probe" or
    n.matches("%_remove%") or
    n.matches("%_shutdown%") or
    n.matches("%_suspend%") or
    n.matches("%_resume%") or
    n.matches("%_open%") or
    n.matches("%_release%") or
    n.matches("%_work%") or
    n.matches("%_thread%")
  )
}

/**
 * Holds if `f` is plausibly an atomic-context function we should
 * NOT flag: interrupt handlers, tasklets, timer callbacks, generic
 * callbacks.
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
 * Holds if `fc` is a long `mdelay` call whose enclosing function `f`
 * looks sleepable and is not flagged as atomic.
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
