/**
 * @name  rq3-c2-dgfp-1-rep4
 * @id    cpp/rq3/c2/dgfp-1-rep4
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2. Detects
 *              mdelay() calls in sleepable context where msleep() would be
 *              appropriate (delay-gfp pattern).
 */

import cpp

/** A direct call to the mdelay() busy-wait helper. */
predicate is_mdelay_call(FunctionCall mc) {
  mc.getTarget().getName() = "mdelay"
}

/** The delay argument (in milliseconds) is large enough that msleep is preferable. */
predicate is_long_delay(FunctionCall mc) {
  is_mdelay_call(mc) and
  exists(Expr arg | arg = mc.getArgument(0) |
    arg.getValue().toInt() >= 10
  )
}

/** A function whose name indicates it is invoked from sleepable / process context
 *  (PM resume/suspend handlers, probe/remove, init/exit, open/release, etc.). */
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

/** An mdelay() call sits inside a sleepable function and uses a long delay
 *  (i.e. msleep() would be more appropriate than busy-waiting). */
predicate mdelay_in_sleepable_context(FunctionCall mc) {
  is_mdelay_call(mc) and
  is_long_delay(mc) and
  is_sleepable_function(mc.getEnclosingFunction())
}

from FunctionCall mc, Function f
where
  mdelay_in_sleepable_context(mc) and
  f = mc.getEnclosingFunction()
select mc,
  "mdelay() called in sleepable function '" + f.getName() +
  "'; consider replacing with msleep() to avoid busy-waiting."
