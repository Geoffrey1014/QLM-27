/**
 * @name delay-gfp: mdelay in sleepable context
 * @description Detects mdelay() calls (busy-wait >= 10 ms) inside functions
 *              whose name suggests a sleepable kernel context
 *              (probe / init / resume / suspend / work / thread / open),
 *              excluding contexts whose name suggests they are atomic
 *              (irq / handler / atomic / nmi / critical / locked / tasklet).
 *              The fix is to replace mdelay() with msleep() or usleep_range().
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3/c3/dgfp-2-rep4/mdelay-in-sleepable
 * @tags correctness performance
 */
import cpp

predicate isBusyDelayCall(FunctionCall fc) {
  fc.getTarget().getName() = "mdelay" and
  exists(fc.getArgument(0).getValue().toInt()) and
  fc.getArgument(0).getValue().toInt() >= 10
}

predicate inSleepableContextByName(Function f) {
  exists(string n | n = f.getName() and
    (n.matches("%resume%") or
     n.matches("%suspend%") or
     n.matches("%probe%") or
     n.matches("%_init%") or
     n.matches("%init_%") or
     n.matches("%work%") or
     n.matches("%thread%") or
     n.matches("%open%")))
}

predicate inAtomicContextByName(Function f) {
  exists(string n | n = f.getName() and
    (n.matches("%irq%") or
     n.matches("%handler%") or
     n.matches("%atomic%") or
     n.matches("%nmi%") or
     n.matches("%critical%") or
     n.matches("%locked%") or
     n.matches("%tasklet%")))
}

from FunctionCall fc, Function caller
where
  isBusyDelayCall(fc) and
  caller = fc.getEnclosingFunction() and
  inSleepableContextByName(caller) and
  not inAtomicContextByName(caller)
select fc,
  "mdelay() in sleepable context (" + caller.getName() +
  "); should be msleep()/usleep_range()."
