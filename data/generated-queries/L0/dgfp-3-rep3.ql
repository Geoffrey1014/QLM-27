/**
 * @name  rq3-l0-dgfp-3-rep3
 * @id    cpp/rq3/l0/dgfp-3-rep3
 * @kind  problem
 * @problem.severity warning
 * @description Zero-shot compositional (L0) query for RQ4 delay-gfp pattern.
 *              Single predicate + assembly (no per-predicate refine, no
 *              assemble-refine). Flags kzalloc()/kmalloc() calls that pass
 *              GFP_ATOMIC inside sleepable init/probe callbacks that are not
 *              IRQ handlers and do not sit inside a spin-lock or IRQ-disabled
 *              region.
 *              Seed: a0732548ba03 (tipc net/tipc/bcast.c tipc_bcast_init).
 */

import cpp

predicate atomicAllocInSleepableContext(FunctionCall fc) {
  (
    fc.getTarget().getName() = "kzalloc" or
    fc.getTarget().getName() = "kmalloc" or
    fc.getTarget().getName() = "kcalloc" or
    fc.getTarget().getName() = "kmalloc_array"
  )
  and fc.getArgument(1).toString().matches("%GFP_ATOMIC%")
  and exists(Function enclosing | enclosing = fc.getEnclosingFunction() |
    (
      enclosing.getName().matches("%_init") or
      enclosing.getName().matches("%_probe") or
      enclosing.getName().matches("%_module_init") or
      enclosing.getName().matches("%bcast_init%") or
      enclosing.getName().matches("%driver_init%") or
      enclosing.getName().matches("%link_init%")
    )
    and not enclosing.getName().matches("%_irq_handler%")
    and not enclosing.getName().matches("%_isr%")
    and not enclosing.getName().matches("%_interrupt%")
    and not exists(FunctionCall lockfc |
      lockfc.getEnclosingFunction() = enclosing and
      (
        lockfc.getTarget().getName() = "spin_lock" or
        lockfc.getTarget().getName() = "spin_lock_irq" or
        lockfc.getTarget().getName() = "spin_lock_irqsave" or
        lockfc.getTarget().getName() = "spin_lock_bh" or
        lockfc.getTarget().getName() = "local_irq_disable" or
        lockfc.getTarget().getName() = "local_irq_save" or
        lockfc.getTarget().getName() = "preempt_disable" or
        lockfc.getTarget().getName() = "rcu_read_lock"
      )
    )
  )
}

from FunctionCall fc
where atomicAllocInSleepableContext(fc)
select fc,
  "kzalloc/kmalloc with GFP_ATOMIC in a sleepable initialization context; consider GFP_KERNEL."
