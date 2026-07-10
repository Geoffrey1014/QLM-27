/**
 * @name Unnecessary GFP_ATOMIC in sleepable context (delay-gfp pattern) [L0]
 * @description Zero-shot (L0) single-predicate query for the RQ4 delay-gfp
 *              pattern. Flags kzalloc/kmalloc/kcalloc calls passing
 *              GFP_ATOMIC from a function whose name suggests a sleepable
 *              init / probe / setup / resume / suspend / work context and
 *              is NOT an IRQ / handler / atomic / tasklet function; and no
 *              spin_lock / preempt_disable / rcu_read_lock is opened
 *              earlier in the same function. Such allocations should use
 *              GFP_KERNEL so the allocator can sleep/reclaim.
 *
 *              L0 ablation: single predicate (all logic in one predicate),
 *              no per-predicate compile-repair, no assemble-refine.
 *              Seed: dgfp-3 / commit a0732548ba03 (net/tipc/bcast.c
 *              tipc_bcast_init GFP_ATOMIC->GFP_KERNEL).
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3/l0/dgfp-3-rep5
 * @tags reliability
 *       performance
 *       delay-gfp
 */

import cpp

predicate isAtomicAllocCallInSleepableContext(FunctionCall fc) {
  (
    fc.getTarget().getName() = "kzalloc" or
    fc.getTarget().getName() = "kmalloc" or
    fc.getTarget().getName() = "kcalloc" or
    fc.getTarget().getName() = "kmalloc_array" or
    fc.getTarget().getName() = "vmalloc"
  )
  and exists(Expr flag |
    flag = fc.getAnArgument() and
    (
      flag.toString() = "GFP_ATOMIC" or
      flag.getValue() = "32" or
      exists(MacroInvocation mi |
        mi.getMacroName() = "GFP_ATOMIC" and mi.getExpr() = flag)
    )
  )
  and exists(Function caller | caller = fc.getEnclosingFunction() |
    (
      caller.getName().matches("%init%") or
      caller.getName().matches("%probe%") or
      caller.getName().matches("%setup%") or
      caller.getName().matches("%resume%") or
      caller.getName().matches("%suspend%") or
      caller.getName().matches("%work%")
    )
    and not caller.getName().matches("%irq%")
    and not caller.getName().matches("%isr%")
    and not caller.getName().matches("%handler%")
    and not caller.getName().matches("%atomic%")
    and not caller.getName().matches("%nmi%")
    and not caller.getName().matches("%tasklet%")
    and not caller.getName().matches("%softirq%")
    and not exists(FunctionCall lockCall |
      lockCall.getEnclosingFunction() = caller and
      (
        lockCall.getTarget().getName() = "spin_lock" or
        lockCall.getTarget().getName() = "spin_lock_irq" or
        lockCall.getTarget().getName() = "spin_lock_irqsave" or
        lockCall.getTarget().getName() = "spin_lock_bh" or
        lockCall.getTarget().getName() = "local_irq_save" or
        lockCall.getTarget().getName() = "local_irq_disable" or
        lockCall.getTarget().getName() = "preempt_disable" or
        lockCall.getTarget().getName() = "rcu_read_lock"
      )
      and lockCall.getLocation().getStartLine() < fc.getLocation().getStartLine()
    )
  )
}

from FunctionCall fc, Function caller
where
  isAtomicAllocCallInSleepableContext(fc) and
  caller = fc.getEnclosingFunction()
select fc,
  "unnecessary GFP_ATOMIC in sleepable context (" + caller.getName() + ")"
