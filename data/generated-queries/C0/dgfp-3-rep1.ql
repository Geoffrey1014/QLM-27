/**
 * @name Unnecessary GFP_ATOMIC in non-atomic context
 * @description Allocation functions (kmalloc/kzalloc/kcalloc/krealloc/kmem_cache_alloc/...)
 *              called with GFP_ATOMIC inside a function that is never invoked from an
 *              atomic context. GFP_ATOMIC unnecessarily depletes the small emergency
 *              memory pool and should be replaced with GFP_KERNEL when sleeping is allowed.
 * @kind problem
 * @problem.severity warning
 * @id cpp/linux-unnecessary-gfp-atomic
 * @tags reliability
 *       performance
 *       linux-kernel
 */

import cpp

/** A kernel allocation function whose last argument is a `gfp_t` flag. */
class GfpAllocFunction extends Function {
  GfpAllocFunction() {
    this.getName() in [
        "kmalloc", "kzalloc", "kcalloc", "kmalloc_array", "kmalloc_node",
        "kzalloc_node", "kcalloc_node", "krealloc", "krealloc_array",
        "kmem_cache_alloc", "kmem_cache_alloc_node", "kmem_cache_zalloc",
        "kmemdup", "kstrdup", "kstrndup", "kvmalloc", "kvzalloc",
        "kvmalloc_node", "kvzalloc_node", "kvcalloc",
        "__vmalloc", "vmalloc", "vzalloc",
        "alloc_skb", "__alloc_skb", "dev_alloc_skb", "netdev_alloc_skb",
        "alloc_pages", "__get_free_pages", "get_zeroed_page",
        "mempool_alloc"
      ]
  }
}

/** A call to an allocation function whose gfp flag argument mentions GFP_ATOMIC. */
class GfpAtomicAllocCall extends FunctionCall {
  GfpAtomicAllocCall() {
    this.getTarget() instanceof GfpAllocFunction and
    exists(Expr flag | flag = this.getAnArgument() |
      flag.toString().matches("%GFP_ATOMIC%") or
      flag.getAChild*().toString().matches("%GFP_ATOMIC%")
    )
  }
}

/** Atomic-context primitives: holding any of these implies atomic context. */
predicate isAtomicEntryFunction(Function f) {
  // IRQ handlers and tasklet/softirq style callbacks usually have these suffixes,
  // or take `irqreturn_t` as the return type.
  f.getType().getName() = "irqreturn_t"
  or
  // BH/tasklet/timer callbacks
  f.getName().matches("%_isr") or
  f.getName().matches("%_irq_handler") or
  f.getName().matches("%_interrupt") or
  f.getName().matches("%_tasklet") or
  f.getName().matches("%_softirq")
}

/** A call that acquires a spinlock / disables preemption / enters RCU read side. */
predicate acquiresAtomic(FunctionCall fc) {
  fc.getTarget().getName() in [
      "spin_lock", "spin_lock_bh", "spin_lock_irq", "spin_lock_irqsave",
      "spin_trylock", "spin_trylock_bh", "spin_trylock_irq", "spin_trylock_irqsave",
      "read_lock", "read_lock_bh", "read_lock_irq", "read_lock_irqsave",
      "write_lock", "write_lock_bh", "write_lock_irq", "write_lock_irqsave",
      "rcu_read_lock", "rcu_read_lock_bh", "rcu_read_lock_sched",
      "preempt_disable", "local_irq_disable", "local_irq_save",
      "local_bh_disable", "raw_spin_lock", "raw_spin_lock_irq",
      "raw_spin_lock_irqsave", "raw_spin_lock_bh"
    ]
}

/**
 * Function `f` is *possibly* called from an atomic context: either it is an
 * atomic-entry function (IRQ handler etc.), or some caller holds a lock /
 * disables preemption before calling it, or it is reachable (depth-limited)
 * from such a caller.
 */
predicate possiblyAtomic(Function f) {
  isAtomicEntryFunction(f)
  or
  // Function itself acquires an atomic primitive and then performs the call
  // (we cannot easily order within one function in a single-shot query;
  //  err on the safe side: if the function has any atomic-acquire, treat as atomic).
  exists(FunctionCall fc | fc.getEnclosingFunction() = f and acquiresAtomic(fc))
  or
  // Recursive: any caller of `f` is possibly atomic
  exists(FunctionCall caller |
    caller.getTarget() = f and
    possiblyAtomic(caller.getEnclosingFunction())
  )
}

/**
 * Heuristic: functions whose names strongly suggest cold init/setup paths
 * that the kernel only invokes during module load / probe / open, never
 * from interrupt or lock-held context.
 */
predicate looksLikeInitPath(Function f) {
  f.getName().matches("%_init") or
  f.getName().matches("init_%") or
  f.getName().matches("%_probe") or
  f.getName().matches("%_setup") or
  f.getName().matches("%_create") or
  f.getName().matches("%_alloc") or
  f.getName().matches("%_open") or
  f.getName().matches("%_register") or
  f.hasName("probe")
}

from GfpAtomicAllocCall call, Function enclosing
where
  enclosing = call.getEnclosingFunction() and
  // Restrict to init-ish paths to keep precision reasonable
  looksLikeInitPath(enclosing) and
  // Filter out anything reachable from atomic context
  not possiblyAtomic(enclosing) and
  // Exclude header/inline noise: must be defined in a .c file
  enclosing.getFile().getExtension() = "c"
select call,
  "Call to '" + call.getTarget().getName() +
    "' uses GFP_ATOMIC inside non-atomic function '" + enclosing.getName() +
    "'; consider GFP_KERNEL."
