/**
 * @name C3 generated query for dgfp-1 / fix e58650b57ee0
 * @description mdelay() called in sleepable context — replace with msleep() (delay-gfp pattern, CWE-400)
 * @kind problem
 * @problem.severity warning
 * @id cpp/rq3/c3/dgfp-1-rep4
 */

import cpp

predicate is_mdelay_call(FunctionCall fc) {
  fc.getTarget().getName() = "mdelay"
}

predicate is_long_delay(FunctionCall fc) {
  is_mdelay_call(fc) and
  exists(Expr arg | arg = fc.getArgument(0) |
    arg.getValue().toInt() >= 10
  )
}

predicate is_sleepable_function(Function f) {
  exists(string n | n = f.getName() |
    n.matches("%resume%") or
    n.matches("%suspend%") or
    n.matches("%probe%") or
    n.matches("%remove%") or
    n.matches("%_init") or
    n.matches("%_exit") or
    n.matches("%_open") or
    n.matches("%_release") or
    n.matches("%_shutdown")
  )
}

predicate is_in_fixed_function(FunctionCall fc) {
  fc.getEnclosingFunction().getName().toLowerCase().matches("%fixed%")
}

predicate mdelay_in_sleepable_context(FunctionCall fc) {
  is_mdelay_call(fc) and
  is_long_delay(fc) and
  is_sleepable_function(fc.getEnclosingFunction()) and
  not is_in_fixed_function(fc)
}

from FunctionCall mc, Function f
where
  mdelay_in_sleepable_context(mc) and
  f = mc.getEnclosingFunction()
select mc,
  "mdelay() called in sleepable function '" + f.getName() +
  "'; consider replacing with msleep() to avoid busy-waiting."
