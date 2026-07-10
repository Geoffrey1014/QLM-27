/**
 * @name mdelay in sleepable-context callback (delay-gfp)
 * @description Detects calls to mdelay() (busy-wait) inside functions
 *              whose names indicate a process/sleepable context
 *              (resume/suspend/probe/init/open/release/remove).
 *              In such contexts msleep() should be used instead, so
 *              the CPU is yielded rather than spun.
 * @kind problem
 * @problem.severity warning
 * @id qlm/l0-dgfp1-mdelay-in-sleepable-context
 */
import cpp

predicate isBusyDelayCall(FunctionCall fc) {
  fc.getTarget().getName() = "mdelay"
}

from FunctionCall delayCall, Function enclosing
where isBusyDelayCall(delayCall)
  and enclosing = delayCall.getEnclosingFunction()
  and (
    enclosing.getName().toLowerCase().matches("%resume%") or
    enclosing.getName().toLowerCase().matches("%suspend%") or
    enclosing.getName().toLowerCase().matches("%probe%") or
    enclosing.getName().toLowerCase().matches("%_init%") or
    enclosing.getName().toLowerCase().matches("init_%") or
    enclosing.getName().toLowerCase().matches("%_open") or
    enclosing.getName().toLowerCase().matches("%_release") or
    enclosing.getName().toLowerCase().matches("%_remove")
  )
select delayCall,
  "mdelay() busy-waits; enclosing function '" + enclosing.getName() +
  "' looks like a sleepable-context callback (resume/suspend/probe/init/open/release/remove). Consider msleep() instead."
