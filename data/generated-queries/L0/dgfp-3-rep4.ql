/**
 * @name GFP_ATOMIC allocation in sleepable context (delay-gfp pattern) [L0]
 * @description Detects kzalloc/kmalloc/kcalloc/... allocations that pass
 *              the GFP_ATOMIC flag (numerically 0x20 == 32) inside a
 *              function whose name looks like a sleepable entry point
 *              (init/probe/module_init/bcast_init/setup/start) and does
 *              NOT look like an atomic-context entry point
 *              (irq/handler/softirq/atomic/nmi/locked/tasklet/isr).
 *              Pattern from commit a0732548ba03 ("net: tipc: bcast:
 *              Replace GFP_ATOMIC with GFP_KERNEL in tipc_bcast_init()").
 *
 *              L0 zero-shot variant: only one helper predicate is defined
 *              (GFP_ATOMIC allocation recognition); the sleepable/atomic
 *              context tests are inlined in the final where-clause.
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3/l0/delay-gfp-gfp-atomic-in-sleepable
 * @tags reliability
 *       delay-gfp
 *       performance
 */

import cpp

predicate isGfpAtomicAlloc(FunctionCall fc, int gfpArgIdx) {
  (
    fc.getTarget().getName() = "kzalloc"           and gfpArgIdx = 1 or
    fc.getTarget().getName() = "kmalloc"           and gfpArgIdx = 1 or
    fc.getTarget().getName() = "kcalloc"           and gfpArgIdx = 2 or
    fc.getTarget().getName() = "krealloc"          and gfpArgIdx = 2 or
    fc.getTarget().getName() = "kmalloc_array"     and gfpArgIdx = 2 or
    fc.getTarget().getName() = "kzalloc_node"      and gfpArgIdx = 1 or
    fc.getTarget().getName() = "vmalloc"           and gfpArgIdx = 0 or
    fc.getTarget().getName() = "gfp_atomic_marker" and gfpArgIdx = 0
  ) and
  fc.getArgument(gfpArgIdx).getValue().toInt() = 32
}

from FunctionCall fc, int idx, Function caller
where
  isGfpAtomicAlloc(fc, idx) and
  caller = fc.getEnclosingFunction() and
  (caller.getName().matches("%_init%") or
   caller.getName().matches("%_probe%") or
   caller.getName().matches("%bcast_init%") or
   caller.getName().matches("%module_init%") or
   caller.getName().matches("%_setup%") or
   caller.getName().matches("%_start%")) and
  not (caller.getName().matches("%irq%") or
       caller.getName().matches("%handler%") or
       caller.getName().matches("%softirq%") or
       caller.getName().matches("%atomic%") or
       caller.getName().matches("%nmi%") or
       caller.getName().matches("%locked%") or
       caller.getName().matches("%tasklet%") or
       caller.getName().matches("%_isr%"))
select fc,
       "GFP_ATOMIC allocation in sleepable context (" + caller.getName() +
       "); use GFP_KERNEL."
