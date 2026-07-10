/**
 * @name  rq3-c2-dgfp-5-rep5
 * @id    cpp/rq3/c2/dgfp-5-rep5
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2 (delay-good-for-process).
 */
import cpp

/** A call to the busy-wait API `mdelay`. */
predicate isMdelayCall(FunctionCall fc) {
  fc.getTarget().getName() = "mdelay"
}

/** A well-known kernel function that may sleep / yield CPU. */
predicate isSleepingFunction(Function f) {
  f.getName() = "msleep" or
  f.getName() = "msleep_interruptible" or
  f.getName() = "usleep_range" or
  f.getName() = "schedule" or
  f.getName() = "schedule_timeout" or
  f.getName() = "mutex_lock" or
  f.getName() = "mutex_lock_interruptible" or
  f.getName() = "down" or
  f.getName() = "down_interruptible" or
  f.getName() = "wait_event" or
  f.getName() = "wait_event_interruptible" or
  f.getName() = "wait_for_completion" or
  f.getName() = "kmalloc" and f.getNumberOfParameters() = 2 // process-ctx allocs are common indicator
}

/** A function whose enclosing function directly calls a sleeping function. */
predicate functionCallsSleeping(Function f) {
  exists(FunctionCall c | c.getEnclosingFunction() = f and isSleepingFunction(c.getTarget()))
}

/** Heuristic: function names that strongly suggest process context. */
predicate hasProcessContextNameHint(Function f) {
  exists(string n | n = f.getName() |
    n.matches("%_probe") or
    n.matches("%_remove") or
    n.matches("%_write") or
    n.matches("%_read") or
    n.matches("%_store") or
    n.matches("%_show") or
    n.matches("%_ioctl") or
    n.matches("%_open") or
    n.matches("%_release") or
    n.matches("%_work%") or
    n.matches("%_handler") or
    n.matches("%cmd_handler%") or
    n.matches("%_thread") or
    n.matches("%_fops%")
  )
}

/** Top: mdelay called from a function that looks like process context. */
predicate mdelayInProcessContext(FunctionCall fc, Function enclosing) {
  isMdelayCall(fc) and
  enclosing = fc.getEnclosingFunction() and
  (functionCallsSleeping(enclosing) or hasProcessContextNameHint(enclosing))
}

from FunctionCall fc, Function enclosing
where mdelayInProcessContext(fc, enclosing)
select fc, "mdelay() called in likely process context (in $@); consider usleep_range().",
  enclosing, enclosing.getName()
