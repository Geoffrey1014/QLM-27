/**
 * @name mdelay() called in sleepable context (use msleep instead)
 * @description Detects calls to the busy-wait kernel API `mdelay()`
 *              (and its long-delay aliases) inside functions that
 *              clearly run in sleepable (process) context: PM
 *              suspend/resume callbacks, probe/remove/open/close
 *              handlers, ioctl/read/write handlers, module init/exit,
 *              workqueue handlers, etc. In such contexts the CPU
 *              should be yielded with msleep()/usleep_range() rather
 *              than busy-spun. This is the DCNS / delay-gfp pattern
 *              (Bai et al., 2018).
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-dgfp-1
 * @tags correctness
 *       performance
 *       kernel
 */

import cpp

/* The busy-wait family of millisecond-scale delay APIs. */
predicate isBusyWaitDelayApi(string name) {
  name = "mdelay"
}

/* Names of caller-supplied delay-amount arguments that are "long".
 * Used only to keep messaging precise; not a filter. */
predicate looksLikeLongDelay(Expr e) {
  exists(int v | v = e.getValue().toInt() and v >= 10)
  or
  not exists(e.getValue())
}

/* Heuristics for sleepable kernel context: the enclosing function's
 * name strongly suggests it runs in process context (not IRQ / softirq
 * / spinlock-held / RCU read-side). Conservative: we only flag when
 * the caller name unambiguously implies sleepable context.
 *
 * NOTE: we deliberately use only the name; CodeQL on the kernel cannot
 * cheaply prove "no spinlock held anywhere on the call chain". The
 * name-based heuristic mirrors how DCNS bootstraps its analysis. */
predicate sleepableContextFunction(Function f) {
  exists(string n, string tok |
    n = f.getName() and
    tok = ["resume", "suspend", "probe", "remove", "open", "release",
           "close", "init", "exit", "ioctl", "read", "write", "show",
           "store", "thread", "work", "worker", "workfn", "reset",
           "setup", "start", "stop", "attach", "detach"] |
    n.matches("%_" + tok) or
    n.matches("%_" + tok + "_%") or
    n = tok
  )
}

/* Exclude functions whose name suggests atomic / hardirq context to
 * keep precision up on the full kernel DB. (No effect on the POC.) */
predicate atomicContextFunction(Function f) {
  exists(string n | n = f.getName() |
    n.matches("%_isr") or
    n.matches("%_irq_handler") or
    n.matches("%_interrupt") or
    n.matches("%_irq") or
    n.matches("%_tasklet") or
    n.matches("%_softirq") or
    n.matches("%_nmi") or
    n.matches("%_atomic")
  )
}

from FunctionCall fc, Function caller, string apiName, Expr arg
where
  apiName = fc.getTarget().getName() and
  isBusyWaitDelayApi(apiName) and
  caller = fc.getEnclosingFunction() and
  sleepableContextFunction(caller) and
  not atomicContextFunction(caller) and
  arg = fc.getArgument(0) and
  looksLikeLongDelay(arg)
select fc,
  "Busy-wait " + apiName + "() called in sleepable context (function '" +
    caller.getName() + "'); prefer msleep()/usleep_range()."
