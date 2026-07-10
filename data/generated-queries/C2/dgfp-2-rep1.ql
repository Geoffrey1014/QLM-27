/**
 * @name  rq3-c2-dgfp-2-rep1
 * @id    cpp/rq3/c2/dgfp-2-rep1
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects mdelay() calls in sleepable contexts (reachable from probe
 *              entry points) where msleep() should be used instead.
 */

import cpp

predicate isMdelayCall(FunctionCall fc) {
  fc.getTarget().getName() = "mdelay"
}

predicate isProbeEntry(Function f) {
  f.getName().matches("%_probe")
  or
  exists(FunctionAccess fa, Initializer init |
    fa.getTarget() = f and
    fa.getEnclosingElement+() = init
  )
  or
  f.getName() = "probe"
}

predicate reachableFromProbe(Function f) {
  isProbeEntry(f)
  or
  exists(Function caller, FunctionCall fc |
    reachableFromProbe(caller) and
    fc.getEnclosingFunction() = caller and
    fc.getTarget() = f
  )
}

predicate inSleepableContext(FunctionCall fc) {
  reachableFromProbe(fc.getEnclosingFunction())
}

predicate isBuggyMdelay(FunctionCall fc) {
  isMdelayCall(fc) and
  inSleepableContext(fc)
}

from FunctionCall fc
where isBuggyMdelay(fc)
select fc, "mdelay called in sleepable (probe-reachable) context; consider msleep instead"
