/**
 * @name Unnecessary GFP_ATOMIC in non-atomic context
 * @description Finds calls that pass GFP_ATOMIC where the enclosing function is
 *              never invoked from atomic context, meaning GFP_KERNEL would be
 *              safer (avoids stressing the atomic allocator reserve pool).
 *              Pattern: a memory/URB-allocating call uses GFP_ATOMIC but the
 *              containing function is not reachable from any spinlock/IRQ/
 *              preempt-disabled site and does not itself disable preemption.
 * @kind problem
 * @problem.severity warning
 * @id cpp/unnecessary-gfp-atomic
 * @tags correctness
 *       performance
 *       linux-kernel
 */

import cpp

/** A macro reference whose name is `GFP_ATOMIC`. */
class GfpAtomicMacro extends MacroInvocation {
  GfpAtomicMacro() { this.getMacroName() = "GFP_ATOMIC" }
}

/**
 * Holds if `e` is an expression syntactically produced by the `GFP_ATOMIC`
 * macro (the macro expands to a bitwise OR expression / integer literal).
 */
predicate isGfpAtomicExpr(Expr e) {
  exists(GfpAtomicMacro m | m.getAnExpandedElement() = e)
}

/**
 * A call which takes a gfp_t flag argument that we know how to recognise.
 * We look at well-known kernel allocator / urb-submission APIs whose last
 * argument is the gfp flag.
 */
class GfpFlagCall extends FunctionCall {
  int gfpArgIndex;

  GfpFlagCall() {
    exists(string n | n = this.getTarget().getName() |
      // URB / USB
      n = "usb_submit_urb" and gfpArgIndex = 1
      or
      n = "usb_alloc_urb" and gfpArgIndex = 1
      or
      // generic kernel allocators
      n = "kmalloc" and gfpArgIndex = 1
      or
      n = "kzalloc" and gfpArgIndex = 1
      or
      n = "kcalloc" and gfpArgIndex = 2
      or
      n = "krealloc" and gfpArgIndex = 2
      or
      n = "kmalloc_array" and gfpArgIndex = 2
      or
      n = "kmem_cache_alloc" and gfpArgIndex = 1
      or
      n = "vmalloc" and gfpArgIndex = 1
      or
      n = "alloc_skb" and gfpArgIndex = 1
      or
      n = "__alloc_skb" and gfpArgIndex = 1
      or
      n = "skb_clone" and gfpArgIndex = 1
      or
      n = "dma_alloc_coherent" and gfpArgIndex = 3
    )
  }

  Expr getGfpArg() { result = this.getArgument(gfpArgIndex) }
}

/** Functions whose names indicate they run in atomic context. */
predicate looksAtomicByName(Function f) {
  exists(string n | n = f.getName() |
    n.matches("%_irq")
    or
    n.matches("%_irqsave")
    or
    n.matches("%_isr")
    or
    n.matches("%_interrupt")
    or
    n.matches("%_handler")
    or
    n.matches("%_callback")
    or
    n.matches("%_tasklet")
    or
    n.matches("%_timer")
    or
    n.matches("%_complete") // urb completion runs in atomic
    or
    n.matches("%_completion")
  )
}

/** Sites that put the caller into atomic context. */
predicate entersAtomic(FunctionCall c) {
  exists(string n | n = c.getTarget().getName() |
    n = "spin_lock"
    or
    n = "spin_lock_bh"
    or
    n = "spin_lock_irq"
    or
    n = "spin_lock_irqsave"
    or
    n = "_raw_spin_lock"
    or
    n = "_raw_spin_lock_irqsave"
    or
    n = "read_lock"
    or
    n = "write_lock"
    or
    n = "rcu_read_lock"
    or
    n = "rcu_read_lock_bh"
    or
    n = "local_irq_disable"
    or
    n = "local_irq_save"
    or
    n = "preempt_disable"
  )
}

/** Function that directly enters atomic context. */
predicate directlyAtomic(Function f) { exists(FunctionCall c | c.getEnclosingFunction() = f and entersAtomic(c)) }

/**
 * A function plausibly running in atomic context: either it's named like an
 * IRQ/completion handler, it directly disables preemption / takes a spinlock,
 * or it is reachable (1-hop) from a function that does.
 */
predicate maybeAtomic(Function f) {
  looksAtomicByName(f)
  or
  directlyAtomic(f)
}

/** Holds if `caller` calls `callee` directly. */
predicate calls(Function caller, Function callee) {
  exists(FunctionCall fc | fc.getEnclosingFunction() = caller and fc.getTarget() = callee)
}

/** Bounded transitive: callee reachable via up to 2 hops from some atomic-looking root. */
predicate reachableFromAtomic(Function f) {
  maybeAtomic(f)
  or
  exists(Function g | reachableFromAtomic(g) and calls(g, f))
}

from GfpFlagCall call, Function enclosing
where
  isGfpAtomicExpr(call.getGfpArg()) and
  enclosing = call.getEnclosingFunction() and
  not reachableFromAtomic(enclosing) and
  not looksAtomicByName(enclosing) and
  // Exclude functions that themselves take a gfp_t parameter (caller decides context).
  not exists(Parameter p | p = enclosing.getAParameter() and p.getType().getName() = "gfp_t")
select call,
  "Call passes GFP_ATOMIC but enclosing function $@ is not reachable from any atomic context; consider GFP_KERNEL.",
  enclosing, enclosing.getName()
