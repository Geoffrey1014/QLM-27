/**
 * @name  rq3-c2-dgfp-2-rep5
 * @id    cpp/rq3/c2/dgfp-2-rep5
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects mdelay() calls with large durations in likely-sleepable
 *              contexts that should be replaced with msleep().
 */
import cpp

predicate isMdelayCall(FunctionCall fc) {
  fc.getTarget().getName() = "mdelay"
}

predicate mdelayLargeDuration(FunctionCall fc, int ms) {
  isMdelayCall(fc) and
  ms = fc.getArgument(0).getValue().toInt() and
  ms >= 10
}

predicate isLikelySleepableFunction(Function f) {
  exists(string n | n = f.getName() |
    n.matches("%probe%") or
    n.matches("%_init%") or
    n.matches("%_remove%") or
    n.matches("%suspend%") or
    n.matches("%resume%") or
    n.matches("%open%") or
    n.matches("%release%") or
    n.matches("%ioctl%")
  )
  or
  exists(FunctionCall fc2 |
    fc2.getEnclosingFunction() = f and
    (fc2.getTarget().getName() = "msleep" or
     fc2.getTarget().getName() = "ssleep" or
     fc2.getTarget().getName() = "usleep_range" or
     fc2.getTarget().getName() = "schedule" or
     fc2.getTarget().getName() = "schedule_timeout" or
     fc2.getTarget().getName() = "wait_event_interruptible" or
     fc2.getTarget().getName() = "mutex_lock")
  )
}

predicate callsMdelayInSleepableCtx(FunctionCall fc, Function caller, int ms) {
  mdelayLargeDuration(fc, ms) and
  caller = fc.getEnclosingFunction() and
  isLikelySleepableFunction(caller)
}

from FunctionCall fc, Function caller, int ms
where callsMdelayInSleepableCtx(fc, caller, ms)
select fc, "mdelay(" + ms + ") in likely-sleepable function " + caller.getName() + "; consider msleep()."
