/**
 * @name Long mdelay() in non-atomic context (should be msleep)
 * @description A call to mdelay() busy-waits the CPU. When the call site is not
 *              in atomic context (IRQ handler, spinlock-holding helper, etc.)
 *              and the delay is non-trivial, msleep() is preferable so the
 *              CPU can do useful work while the delay elapses.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-dgfp-2
 */

import cpp

/**
 * Conservative name-based heuristic: a function whose name suggests it runs
 * in an atomic / interrupt / lock-held context, where mdelay() is the
 * appropriate (or only) choice.
 */
predicate looksAtomic(Function f) {
  exists(string lname | lname = f.getName().toLowerCase() |
    lname.matches("%_isr") or
    lname.matches("%_irq%") or
    lname.matches("%irq_%") or
    lname.matches("%_handler") or
    lname.matches("%_nmi%") or
    lname.matches("%_interrupt") or
    lname.matches("%_atomic%") or
    lname.matches("%spin_%") or
    lname.matches("%_tasklet%") or
    lname.matches("%poll%")
  )
}

/** Holds if `c` is a call to mdelay with a compile-time constant >= 10 ms. */
predicate longMdelayCall(FunctionCall c, int millis) {
  c.getTarget().getName() = "mdelay" and
  millis = c.getArgument(0).getValue().toInt() and
  millis >= 10
}

from FunctionCall call, Function caller, int ms
where
  longMdelayCall(call, ms) and
  caller = call.getEnclosingFunction() and
  not looksAtomic(caller)
select call,
  "mdelay(" + ms.toString() + ") busy-waits for " + ms.toString() +
  " ms in '" + caller.getName() +
  "', which is not detectably an atomic context; consider msleep()."
