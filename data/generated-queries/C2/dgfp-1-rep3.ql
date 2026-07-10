/**
 * @name  rq3-c2-dgfp-1-rep3
 * @id    cpp/rq3/c2/dgfp-1-rep3
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects mdelay() calls with non-trivial delay used inside
 *              sleepable-context functions (resume/suspend/probe/init/etc.)
 *              where msleep() should be used instead.
 */

import cpp

predicate isMdelayCall(FunctionCall fc) {
  fc.getTarget().getName() = "mdelay"
}

predicate isLargeDelay(FunctionCall fc) {
  isMdelayCall(fc) and
  exists(Expr arg | arg = fc.getArgument(0) |
    arg.getValue().toInt() >= 10
  )
}

predicate isSleepableContext(Function f) {
  exists(string n | n = f.getName() |
    n.matches("%resume%") or
    n.matches("%suspend%") or
    n.matches("%probe%") or
    n.matches("%_init") or
    n.matches("%_open") or
    n.matches("%_release") or
    n.matches("%_remove")
  )
}

predicate mdelayInSleepable(FunctionCall fc, Function f) {
  isLargeDelay(fc) and
  isSleepableContext(f) and
  fc.getEnclosingFunction() = f
}

from FunctionCall fc, Function f
where mdelayInSleepable(fc, f)
select fc, "mdelay() with large delay in sleepable context (function " + f.getName() + "); should use msleep()"
