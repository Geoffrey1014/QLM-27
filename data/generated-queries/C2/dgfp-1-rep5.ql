/**
 * @name  rq3-c2-dgfp-1-rep5
 * @id    cpp/rq3/c2/dgfp-1-rep5
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects mdelay() calls inside sleepable-context functions
 *              (PM resume/suspend/probe/remove), where msleep() should be used.
 */
import cpp

predicate isMdelayCall(FunctionCall fc) {
  fc.getTarget().getName() = "mdelay"
}

predicate isSleepableContext(Function f) {
  f.getName().regexpMatch(".*_resume") or
  f.getName().regexpMatch(".*_suspend") or
  f.getName().regexpMatch(".*_probe") or
  f.getName().regexpMatch(".*_remove") or
  f.getName().regexpMatch(".*_runtime_resume") or
  f.getName().regexpMatch(".*_runtime_suspend") or
  exists(Attribute a | a = f.getAnAttribute() and a.getName() = "__maybe_unused")
}

predicate inSleepableFunction(FunctionCall fc) {
  isSleepableContext(fc.getEnclosingFunction())
}

predicate mdelayInSleepableContext(FunctionCall fc) {
  isMdelayCall(fc) and inSleepableFunction(fc)
}

from FunctionCall fc
where mdelayInSleepableContext(fc)
select fc, "mdelay() called in sleepable context function '" +
           fc.getEnclosingFunction().getName() +
           "'; consider replacing with msleep() to avoid busy-waiting."
