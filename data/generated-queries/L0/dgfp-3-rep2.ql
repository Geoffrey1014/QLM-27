/**
 * @name GFP_ATOMIC allocation in sleepable context (delay-gfp pattern) [L0]
 * @description Detects calls to kmalloc/kzalloc/kcalloc/krealloc/kmem_cache_*alloc
 *              and their _node variants that pass GFP_ATOMIC even though the
 *              enclosing function name looks like a sleepable-context entry
 *              point (driver/module init, probe, suspend/resume, workqueue,
 *              kernel thread, open/release/remove/shutdown). Pattern derived
 *              from upstream commit a0732548ba03 ("net: tipc: bcast: replace
 *              GFP_ATOMIC with GFP_KERNEL in tipc_bcast_init()"), of the Bai
 *              et al. delay-gfp findings (USENIX ATC 2018 lineage).
 *
 *              L0 zero-shot variant: only ONE helper predicate is defined
 *              (isGfpAtomicKernelAlloc — allocator name in a fixed set AND
 *              second arg literally GFP_ATOMIC); the sleepable- and
 *              atomic-context name tests are inlined in the assembly
 *              where-clause. No refinement loops (per L0 ablation).
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3/l0/delay-gfp-unneeded-atomic
 * @tags reliability
 *       delay-gfp
 *       performance
 */

import cpp

/* P: GFP-taking kernel allocator called with GFP_ATOMIC literal. */
predicate isGfpAtomicKernelAlloc(FunctionCall fc) {
  fc.getTarget().getName() in [
    "kmalloc", "kzalloc", "kcalloc", "krealloc",
    "kmalloc_array", "kzalloc_node", "kmalloc_node", "kcalloc_node",
    "kmem_cache_alloc", "kmem_cache_zalloc"
  ] and
  fc.getArgument(1).getValueText() = "GFP_ATOMIC"
}

from FunctionCall fc, Function caller
where
  isGfpAtomicKernelAlloc(fc) and
  caller = fc.getEnclosingFunction() and
  (caller.getName().matches("%_init%") or
   caller.getName().matches("%init_%") or
   caller.getName() = "init" or
   caller.getName().matches("%_probe%") or
   caller.getName().matches("%probe_%") or
   caller.getName() = "probe" or
   caller.getName().matches("%_resume%") or
   caller.getName().matches("%_suspend%") or
   caller.getName().matches("%_open") or
   caller.getName().matches("%_release") or
   caller.getName().matches("%_work%") or
   caller.getName().matches("%_thread%") or
   caller.getName().matches("%_remove%") or
   caller.getName().matches("%_shutdown%")) and
  not (caller.getName().matches("%irq%") or
       caller.getName().matches("%handler%") or
       caller.getName().matches("%atomic%") or
       caller.getName().matches("%nmi%") or
       caller.getName().matches("%locked%") or
       caller.getName().matches("%tasklet%") or
       caller.getName().matches("%softirq%") or
       caller.getName().matches("%isr%") or
       caller.getName().matches("%_timer%"))
select fc,
       "GFP_ATOMIC allocation in sleepable context (" + caller.getName() +
       "); use GFP_KERNEL instead"
