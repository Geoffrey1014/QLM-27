/**
 * @name Unnecessary GFP_ATOMIC allocation in non-atomic context
 * @description Detects allocation functions (kmalloc, kzalloc, kcalloc, kmalloc_array,
 *              vmalloc, etc.) called with GFP_ATOMIC inside functions that are never
 *              invoked from atomic context (e.g. *_init, *_probe, *_open, module init).
 *              Using GFP_ATOMIC in such places needlessly stresses the emergency
 *              memory pool; GFP_KERNEL is appropriate.
 * @kind problem
 * @problem.severity warning
 * @id cpp/kernel-unnecessary-gfp-atomic
 * @tags correctness
 *       memory
 *       linux-kernel
 */

import cpp

/** Kernel allocation APIs whose last gfp_t argument controls the alloc flags. */
predicate isKernelAllocFunction(Function f, int gfpArgIndex) {
  exists(string n | n = f.getName() |
    (n = "kmalloc" and gfpArgIndex = 1) or
    (n = "kzalloc" and gfpArgIndex = 1) or
    (n = "kmalloc_node" and gfpArgIndex = 2) or
    (n = "kzalloc_node" and gfpArgIndex = 2) or
    (n = "kcalloc" and gfpArgIndex = 2) or
    (n = "kcalloc_node" and gfpArgIndex = 3) or
    (n = "kmalloc_array" and gfpArgIndex = 2) or
    (n = "kmalloc_array_node" and gfpArgIndex = 3) or
    (n = "krealloc" and gfpArgIndex = 2) or
    (n = "kvmalloc" and gfpArgIndex = 1) or
    (n = "kvzalloc" and gfpArgIndex = 1) or
    (n = "kvmalloc_node" and gfpArgIndex = 2) or
    (n = "kvzalloc_node" and gfpArgIndex = 2) or
    (n = "vmalloc" and gfpArgIndex = -1) or
    (n = "kmem_cache_alloc" and gfpArgIndex = 1) or
    (n = "kmem_cache_zalloc" and gfpArgIndex = 1) or
    (n = "mempool_alloc" and gfpArgIndex = 1) or
    (n = "alloc_skb" and gfpArgIndex = 1) or
    (n = "__alloc_skb" and gfpArgIndex = 1) or
    (n = "alloc_pages" and gfpArgIndex = 0) or
    (n = "__get_free_pages" and gfpArgIndex = 0) or
    (n = "get_zeroed_page" and gfpArgIndex = 0)
  )
}

/** An expression that mentions GFP_ATOMIC (as a macro/enum/identifier). */
predicate mentionsGfpAtomic(Expr e) {
  exists(MacroInvocation mi | mi.getAnExpandedElement() = e and mi.getMacroName() = "GFP_ATOMIC")
  or
  e.toString() = "GFP_ATOMIC"
  or
  exists(Expr child | child = e.getAChild*() | child.toString() = "GFP_ATOMIC")
}

/** A function that is a strong heuristic for "definitely not atomic context". */
predicate isNonAtomicContextFunction(Function f) {
  exists(string n | n = f.getName() |
    n.matches("%_init") or
    n.matches("%_probe") or
    n.matches("%_open") or
    n.matches("%_create") or
    n.matches("%_setup") or
    n.matches("%_register") or
    n = "init" or
    n.matches("init_%") or
    n.matches("probe_%") or
    n.matches("module_init") or
    n.matches("%_module_init") or
    n.matches("%_ioctl") or
    n.matches("%_mmap") or
    n.matches("%_release")
  )
  and
  // Exclude things that explicitly look like IRQ/atomic/timer/tasklet handlers.
  not f.getName().matches("%_irq%") and
  not f.getName().matches("%_isr%") and
  not f.getName().matches("%_handler%") and
  not f.getName().matches("%_tasklet%") and
  not f.getName().matches("%_timer%") and
  not f.getName().matches("%_callback%") and
  not f.getName().matches("%_atomic%") and
  not f.getName().matches("%_nmi%")
}

/** Caller does not appear to take a spinlock / disable preemption / disable IRQs. */
predicate noObviousAtomicGuard(Function caller) {
  not exists(FunctionCall fc | fc.getEnclosingFunction() = caller |
    exists(string n | n = fc.getTarget().getName() |
      n.matches("spin_lock%") or
      n.matches("raw_spin_lock%") or
      n.matches("read_lock%") or
      n.matches("write_lock%") or
      n.matches("rcu_read_lock%") or
      n.matches("preempt_disable%") or
      n.matches("local_irq_disable%") or
      n.matches("local_irq_save%") or
      n.matches("local_bh_disable%")
    )
  )
}

from FunctionCall call, Function alloc, int gfpIdx, Function caller, Expr gfpArg
where
  alloc = call.getTarget() and
  isKernelAllocFunction(alloc, gfpIdx) and
  gfpIdx >= 0 and
  gfpArg = call.getArgument(gfpIdx) and
  mentionsGfpAtomic(gfpArg) and
  caller = call.getEnclosingFunction() and
  isNonAtomicContextFunction(caller) and
  noObviousAtomicGuard(caller)
select call,
  "Unnecessary GFP_ATOMIC in $@ which is called from non-atomic context (" +
  caller.getName() + "); consider GFP_KERNEL.", alloc, alloc.getName()
