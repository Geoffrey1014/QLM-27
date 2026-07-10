/**
 * @name  rq3-c3-dgfp-3-rep1
 * @id    cpp/rq3/c3/dgfp-3-rep1
 * @kind  problem
 * @problem.severity warning
 * @description Full QLM pipeline (compositional + POC + verifier-v1) for
 *              RQ3 cell C3. Flags kzalloc/kmalloc/kcalloc calls that pass
 *              GFP_ATOMIC inside an initialization function (init/probe/
 *              setup/resume/suspend) when no spinlock is held and no IRQ
 *              context surrounds the call. Such allocations should use
 *              GFP_KERNEL because the caller chain reaches the alloc from
 *              process context.
 *              Seed: a0732548ba03 (net/tipc/bcast.c tipc_bcast_init).
 */

import cpp

predicate isAtomicAlloc(FunctionCall fc) {
  exists(string name | name = fc.getTarget().getName() |
    name = "kzalloc" or name = "kmalloc" or name = "kcalloc"
  ) and
  fc.getArgument(1).getValue() = "32"
}

predicate inAtomicContextByName(Function f) {
  exists(string n | n = f.getName() |
    n.matches("%_isr%") or
    n.matches("%_irq_handler%") or
    n.matches("%_interrupt%") or
    n.matches("%irq_handler%") or
    (n.matches("%_handler") and n.matches("%irq%"))
  )
}

predicate isLockHeldAroundCall(FunctionCall fc) {
  exists(Function f, FunctionCall lockCall |
    f = fc.getEnclosingFunction() and
    lockCall.getEnclosingFunction() = f and
    (
      lockCall.getTarget().getName() = "spin_lock" or
      lockCall.getTarget().getName() = "spin_lock_irq" or
      lockCall.getTarget().getName() = "spin_lock_irqsave" or
      lockCall.getTarget().getName() = "spin_lock_bh" or
      lockCall.getTarget().getName() = "local_irq_save" or
      lockCall.getTarget().getName() = "local_irq_disable" or
      lockCall.getTarget().getName() = "preempt_disable" or
      lockCall.getTarget().getName() = "rcu_read_lock"
    ) and
    lockCall.getLocation().getStartLine() < fc.getLocation().getStartLine()
  )
}

predicate inSleepableInitFunction(Function f) {
  not inAtomicContextByName(f) and
  exists(string n | n = f.getName() |
    n.matches("%_init%") or
    n.matches("%_probe%") or
    n.matches("%_setup%") or
    n.matches("%setup_%") or
    n.matches("%probe_%") or
    n.matches("%driver_init%") or
    n.matches("%bcast_init%") or
    n.matches("%device_init%") or
    n.matches("%_resume%") or
    n.matches("%_suspend%")
  )
}

from FunctionCall alloc, Function enc
where
  isAtomicAlloc(alloc) and
  enc = alloc.getEnclosingFunction() and
  inSleepableInitFunction(enc) and
  not inAtomicContextByName(enc) and
  not isLockHeldAroundCall(alloc)
select alloc,
  "GFP_ATOMIC used in sleepable initialization context '" + enc.getName() +
  "'; the caller chain establishes process context, so GFP_KERNEL is the correct flag."
