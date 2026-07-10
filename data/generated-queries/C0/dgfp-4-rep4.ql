/**
 * @name Unnecessary GFP_ATOMIC in non-atomic context
 * @description A function passes GFP_ATOMIC to an allocator (e.g. usb_submit_urb,
 *              kmalloc, kzalloc) but the enclosing function is never invoked from
 *              an atomic context (no spinlock held, not an IRQ/timer/tasklet
 *              callback, not called from a function that holds a lock). Using
 *              GFP_ATOMIC unnecessarily depletes the emergency reserves; GFP_KERNEL
 *              should be used instead.
 * @kind problem
 * @problem.severity warning
 * @id cpp/unnecessary-gfp-atomic
 * @tags correctness
 *       performance
 */

import cpp

/** An expression that originates from the GFP_ATOMIC macro. */
class GfpAtomicAccess extends Expr {
  GfpAtomicAccess() {
    exists(MacroInvocation mi |
      mi.getMacroName() = "GFP_ATOMIC" and
      mi.getExpr() = this
    )
  }
}

/** Allocator-like functions that take a gfp_t flag argument. */
class GfpAllocator extends Function {
  int gfpArgIndex;

  GfpAllocator() {
    this.getName() =
      [
        "usb_submit_urb", "kmalloc", "kzalloc", "kcalloc", "krealloc", "kmalloc_node",
        "kzalloc_node", "vmalloc", "vzalloc", "kmem_cache_alloc", "kmem_cache_alloc_node",
        "kmem_cache_zalloc", "alloc_skb", "dev_alloc_skb", "__netdev_alloc_skb",
        "netdev_alloc_skb", "alloc_pages", "__get_free_pages", "get_zeroed_page",
        "mempool_alloc", "dma_alloc_coherent", "dma_pool_alloc", "kvmalloc", "kvzalloc"
      ] and
    (
      this.getName() = "usb_submit_urb" and gfpArgIndex = 1
      or
      this.getName() = ["dma_alloc_coherent"] and gfpArgIndex = 3
      or
      this.getName() = ["dma_pool_alloc"] and gfpArgIndex = 1
      or
      this.getName() = ["kmalloc_node", "kzalloc_node", "kmem_cache_alloc_node"] and gfpArgIndex = 2
      or
      this.getName() = ["kcalloc", "krealloc"] and gfpArgIndex = 2
      or
      not this.getName() =
        [
          "usb_submit_urb", "dma_alloc_coherent", "dma_pool_alloc", "kmalloc_node",
          "kzalloc_node", "kmem_cache_alloc_node", "kcalloc", "krealloc"
        ] and
      gfpArgIndex = 1
    )
  }

  int getGfpArgIndex() { result = gfpArgIndex }
}

/** Calls that pass a GFP_ATOMIC flag to an allocator. */
class AtomicAllocCall extends FunctionCall {
  AtomicAllocCall() {
    exists(GfpAllocator a, int i |
      this.getTarget() = a and
      i = a.getGfpArgIndex() and
      this.getArgument(i) instanceof GfpAtomicAccess
    )
  }
}

/** Functions that obviously execute in atomic context. */
predicate runsInAtomicContext(Function f) {
  // Holds a spinlock-like primitive
  exists(FunctionCall c |
    c.getEnclosingFunction() = f and
    c.getTarget().getName() =
      [
        "spin_lock", "spin_lock_irq", "spin_lock_irqsave", "spin_lock_bh",
        "_raw_spin_lock", "_raw_spin_lock_irq", "_raw_spin_lock_irqsave",
        "read_lock", "read_lock_irq", "read_lock_irqsave", "read_lock_bh",
        "write_lock", "write_lock_irq", "write_lock_irqsave", "write_lock_bh",
        "rcu_read_lock", "rcu_read_lock_bh", "rcu_read_lock_sched",
        "preempt_disable", "local_irq_disable", "local_irq_save",
        "local_bh_disable"
      ]
  )
  or
  // Heuristic: name suggests interrupt/atomic callback
  f.getName().regexpMatch("(?i).*(irq|isr|interrupt|tasklet|timer|softirq|complete|callback)_?(handler|fn|cb|func)?")
  or
  // Used as an interrupt handler / urb completion (taken as function pointer
  // and assigned to a known callback field name)
  exists(FunctionAccess fa, Field field |
    fa.getTarget() = f and
    fa.getEnclosingElement+() = field.getInitializer().getExpr() and
    field.getName() = ["complete", "handler", "isr", "interrupt"]
  )
  or
  // Assigned to urb->complete or similar
  exists(Assignment a, FunctionAccess fa |
    fa = a.getRValue() and
    fa.getTarget() = f and
    a.getLValue().toString().regexpMatch(".*(complete|handler|isr|callback).*")
  )
}

/**
 * Transitive: f is reachable (as callee) from some function that runs in atomic
 * context. We treat such functions as potentially atomic.
 */
predicate reachableFromAtomic(Function f) {
  runsInAtomicContext(f)
  or
  exists(Function caller, FunctionCall c |
    c.getEnclosingFunction() = caller and
    c.getTarget() = f and
    reachableFromAtomic(caller)
  )
}

from AtomicAllocCall call, Function f
where
  f = call.getEnclosingFunction() and
  not reachableFromAtomic(f) and
  // Sanity: function has a definition we can see
  f.hasDefinition() and
  // Exclude obvious atomic-context helpers by name
  not f.getName().regexpMatch("(?i).*(atomic|irq|isr|interrupt|tasklet|complete).*")
select call,
  "Call to $@ uses GFP_ATOMIC, but enclosing function '" + f.getName() +
    "' is not known to run in atomic context; consider GFP_KERNEL.",
  call.getTarget(), call.getTarget().getName()
