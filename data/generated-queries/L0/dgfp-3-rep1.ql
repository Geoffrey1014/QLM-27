/**
 * @name  GFP_ATOMIC used in sleepable init context (delay-gfp pattern) [L0]
 * @description Detects kzalloc/kmalloc/kcalloc calls that pass GFP_ATOMIC
 *              (integer literal 32 after preprocessing) inside an
 *              initialization-flavoured function (init/probe/setup/resume/
 *              suspend/bcast_init) when the enclosing function is neither
 *              named like an atomic-context entry point (irq/isr/handler/
 *              interrupt) nor holds a spinlock / disables preemption / IRQs
 *              / RCU around the allocation site. Such allocations should
 *              use GFP_KERNEL because the caller chain reaches the alloc
 *              from process context. Pattern from commit a0732548ba03
 *              ("net: tipc: bcast: Replace GFP_ATOMIC with GFP_KERNEL in
 *              tipc_bcast_init()").
 *
 *              L0 zero-shot variant: exactly one helper predicate is
 *              defined (isAtomicAlloc); the sleepable-init / atomic-name /
 *              lock-held tests are inlined in the assembly where-clause.
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3/l0/delay-gfp-atomic-alloc-in-init
 * @tags reliability
 *       delay-gfp
 *       performance
 */

import cpp

predicate isAtomicAlloc(FunctionCall fc) {
  exists(string name | name = fc.getTarget().getName() |
    name = "kzalloc" or name = "kmalloc" or name = "kcalloc"
  ) and
  fc.getArgument(1).getValue() = "32"
}

from FunctionCall alloc, Function enc
where
  isAtomicAlloc(alloc) and
  enc = alloc.getEnclosingFunction() and
  (enc.getName().matches("%_init%") or
   enc.getName().matches("%_probe%") or
   enc.getName().matches("%_setup%") or
   enc.getName().matches("%setup_%") or
   enc.getName().matches("%probe_%") or
   enc.getName().matches("%driver_init%") or
   enc.getName().matches("%bcast_init%") or
   enc.getName().matches("%_resume%") or
   enc.getName().matches("%_suspend%")) and
  not (enc.getName().matches("%_isr%") or
       enc.getName().matches("%_irq_handler%") or
       enc.getName().matches("%_interrupt%") or
       enc.getName().matches("%irq_handler%") or
       enc.getName().matches("%_irq%")) and
  not exists(FunctionCall lockCall |
    lockCall.getEnclosingFunction() = enc and
    (lockCall.getTarget().getName() = "spin_lock" or
     lockCall.getTarget().getName() = "spin_lock_irq" or
     lockCall.getTarget().getName() = "spin_lock_irqsave" or
     lockCall.getTarget().getName() = "spin_lock_bh" or
     lockCall.getTarget().getName() = "local_irq_save" or
     lockCall.getTarget().getName() = "local_irq_disable" or
     lockCall.getTarget().getName() = "preempt_disable" or
     lockCall.getTarget().getName() = "rcu_read_lock") and
    lockCall.getLocation().getStartLine() < alloc.getLocation().getStartLine()
  )
select alloc,
  "GFP_ATOMIC used in sleepable initialization context '" + enc.getName() +
  "'; the caller chain establishes process context, so GFP_KERNEL is the correct flag."
