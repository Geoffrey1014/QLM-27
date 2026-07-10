/**
 * @name delay-gfp: GFP_ATOMIC allocation in sleepable context
 * @description Flags kzalloc/kmalloc/kcalloc calls that pass GFP_ATOMIC
 *              from a function whose name suggests a sleepable context
 *              (init / probe / resume / suspend / open / create / setup /
 *              register), with no atomic-context naming hint, so the
 *              allocation should use GFP_KERNEL instead.
 *              Seed: net/tipc/bcast.c tipc_bcast_init() (a0732548ba03).
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3-c3-dgfp-3-rep4
 */
import cpp

predicate isAtomicAllocCall(FunctionCall fc) {
  (fc.getTarget().getName() = "kzalloc" or
   fc.getTarget().getName() = "kmalloc" or
   fc.getTarget().getName() = "kcalloc") and
  exists(Expr gfp | gfp = fc.getArgument(fc.getNumberOfArguments() - 1) |
    gfp.getValue().toInt() = 32 or
    gfp.toString().matches("%GFP_ATOMIC%")
  )
}

predicate inSleepableContextByName(Function f) {
  exists(string n | n = f.getName() and
    (n.matches("%init%") or n.matches("%probe%") or
     n.matches("%resume%") or n.matches("%suspend%") or
     n.matches("%open%") or n.matches("%create%") or
     n.matches("%setup%") or n.matches("%register%")))
}

predicate inAtomicContextByName(Function f) {
  exists(string n | n = f.getName() and
    (n.matches("%irq%") or n.matches("%handler%") or
     n.matches("%atomic%") or n.matches("%nmi%") or
     n.matches("%tasklet%") or n.matches("%isr%") or
     n.matches("%timer%")))
}

from FunctionCall fc, Function caller
where
  isAtomicAllocCall(fc) and
  caller = fc.getEnclosingFunction() and
  inSleepableContextByName(caller) and
  not inAtomicContextByName(caller)
select fc,
  "GFP_ATOMIC allocation in sleepable context (" + caller.getName() +
  "); should use GFP_KERNEL"
