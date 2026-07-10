/**
 * @name  rq3-c2-dgfp-2-rep3
 * @id    cpp/rq3/c2/dgfp-2-rep3
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Flags busy-wait delay calls (mdelay/udelay/...) used inside
 *              functions reachable from sleepable (probe-like) entry points,
 *              where msleep/usleep_range would be preferred.
 */

import cpp

predicate isBusyDelayCall(FunctionCall fc) {
  exists(Function callee | callee = fc.getTarget() |
    callee.getName() = "mdelay" or
    callee.getName() = "udelay" or
    callee.getName() = "ndelay" or
    callee.getName() = "__const_udelay" or
    callee.getName() = "__udelay"
  )
}

predicate isProbeLikeEntry(Function f) {
  f.getName().matches("%probe%") or
  f.getName().matches("%_init") or
  f.getName().matches("init_%") or
  f.getName().matches("%_open") or
  f.getName().matches("%suspend%") or
  f.getName().matches("%resume%") or
  f.getName().matches("%remove%") or
  f.getName().matches("%shutdown%") or
  exists(Initializer init, Expr e |
    e = init.getExpr().getAChild*() and
    e.(FunctionAccess).getTarget() = f and
    init.getDeclaration().getName().toLowerCase().regexpMatch(".*(probe|driver|ops).*")
  )
}

predicate reachableFromProbe(Function callee) {
  isProbeLikeEntry(callee)
  or
  exists(Function caller, FunctionCall fc |
    reachableFromProbe(caller) and
    fc.getEnclosingFunction() = caller and
    fc.getTarget() = callee
  )
}

predicate busyDelayInProbeContext(FunctionCall fc) {
  isBusyDelayCall(fc) and
  reachableFromProbe(fc.getEnclosingFunction())
}

from FunctionCall fc
where busyDelayInProbeContext(fc)
select fc, "mdelay/udelay used in sleepable (probe) context; consider msleep/usleep_range."
