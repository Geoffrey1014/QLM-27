/**
 * @name GFP_ATOMIC allocation in sleepable context (delay-gfp pattern)
 * @description Detects calls to kmalloc/kzalloc/kcalloc/kmem_cache_alloc and
 *              friends that pass GFP_ATOMIC even though the enclosing function
 *              is a sleepable-context entry point (driver/module init, probe,
 *              suspend/resume, workqueue handler, kernel thread). In such
 *              callers GFP_KERNEL is correct; using GFP_ATOMIC needlessly
 *              taps the atomic reserve and can starve callers that genuinely
 *              need it. Pattern derived from upstream commit a0732548ba03
 *              ("net: tipc: bcast: replace GFP_ATOMIC with GFP_KERNEL in
 *              tipc_bcast_init()"), one of the Bai et al. delay-gfp findings
 *              (USENIX ATC 2018 lineage).
 *
 *              The query gates on:
 *                P1. allocation site is a GFP-taking kernel alloc
 *                    (kmalloc/kzalloc/kcalloc/krealloc/kmem_cache_*alloc
 *                    and their _node variants).
 *                P2. the gfp_t argument is GFP_ATOMIC.
 *                P3. the enclosing function name matches a sleepable-context
 *                    shape (init/probe/resume/suspend/work/thread/...).
 *                P4. the enclosing function name does NOT match an atomic
 *                    shape (irq/handler/atomic/nmi/locked/tasklet/...),
 *                    which is where GFP_ATOMIC is genuinely required.
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3/c3/delay-gfp-unneeded-atomic
 * @tags reliability
 *       delay-gfp
 *       performance
 */

import cpp

/* P1: GFP-taking kernel allocator family. */
predicate isGfpAllocCall(FunctionCall fc) {
  fc.getTarget().getName() in [
    "kmalloc", "kzalloc", "kcalloc", "krealloc",
    "kmalloc_array", "kzalloc_node", "kmalloc_node", "kcalloc_node",
    "kmem_cache_alloc", "kmem_cache_zalloc"
  ]
}

/* P2: gfp_t argument expands to GFP_ATOMIC. */
predicate isGfpAtomicArg(Expr e) {
  e.getValueText() = "GFP_ATOMIC"
}

/* P3: enclosing function looks sleepable — module/driver init, probe,
 *     suspend/resume callbacks, workqueue handlers, kernel threads. */
predicate inSleepableContextByName(Function f) {
  exists(string n |
    n = f.getName()
  |
    n.matches("%_init%") or
    n.matches("%init_%") or
    n = "init" or
    n.matches("%_probe%") or
    n.matches("%probe_%") or
    n = "probe" or
    n.matches("%_resume%") or
    n.matches("%_suspend%") or
    n.matches("%_open") or
    n.matches("%_release") or
    n.matches("%_work%") or
    n.matches("%_thread%") or
    n.matches("%_remove%") or
    n.matches("%_shutdown%")
  )
}

/* P4: enclosing function looks atomic — IRQ handler / NMI / tasklet /
 *     softirq / explicit "locked" helper. Excluded so we stay silent on
 *     genuinely-correct GFP_ATOMIC uses. */
predicate inAtomicContextByName(Function f) {
  exists(string n |
    n = f.getName()
  |
    n.matches("%irq%") or
    n.matches("%handler%") or
    n.matches("%atomic%") or
    n.matches("%nmi%") or
    n.matches("%locked%") or
    n.matches("%tasklet%") or
    n.matches("%softirq%") or
    n.matches("%isr%") or
    n.matches("%_timer%")
  )
}

from FunctionCall fc, Function caller
where
  isGfpAllocCall(fc) and
  isGfpAtomicArg(fc.getArgument(1)) and
  caller = fc.getEnclosingFunction() and
  inSleepableContextByName(caller) and
  not inAtomicContextByName(caller)
select fc,
       "GFP_ATOMIC allocation in sleepable context (" + caller.getName() +
       "); use GFP_KERNEL instead"
