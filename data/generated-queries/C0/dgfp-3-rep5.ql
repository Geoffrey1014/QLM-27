/**
 * @name Unnecessary GFP_ATOMIC allocation in non-atomic context
 * @description Detects calls to kernel allocators (kmalloc/kzalloc/kcalloc/krealloc/
 *              kmem_cache_alloc/etc.) that pass GFP_ATOMIC even though the enclosing
 *              function is never invoked from atomic context (no spinlock held, not an
 *              interrupt/softirq/tasklet handler, not called from such). GFP_ATOMIC
 *              uses emergency reserves and can fail more easily; GFP_KERNEL should be
 *              preferred when sleeping is permitted.
 * @kind problem
 * @problem.severity warning
 * @id cpp/unnecessary-gfp-atomic
 * @tags reliability
 *       performance
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph

/** Allocator functions in the kernel that accept a gfp_t flag argument. */
class KernelAllocator extends Function {
  int gfpArgIndex;

  KernelAllocator() {
    (
      this.getName() = "kmalloc" and gfpArgIndex = 1
      or
      this.getName() = "kzalloc" and gfpArgIndex = 1
      or
      this.getName() = "kmalloc_node" and gfpArgIndex = 1
      or
      this.getName() = "kzalloc_node" and gfpArgIndex = 1
      or
      this.getName() = "kcalloc" and gfpArgIndex = 2
      or
      this.getName() = "kcalloc_node" and gfpArgIndex = 2
      or
      this.getName() = "kmalloc_array" and gfpArgIndex = 2
      or
      this.getName() = "kmalloc_array_node" and gfpArgIndex = 2
      or
      this.getName() = "krealloc" and gfpArgIndex = 2
      or
      this.getName() = "kmemdup" and gfpArgIndex = 2
      or
      this.getName() = "kstrdup" and gfpArgIndex = 1
      or
      this.getName() = "kstrndup" and gfpArgIndex = 2
      or
      this.getName() = "kmem_cache_alloc" and gfpArgIndex = 1
      or
      this.getName() = "kmem_cache_zalloc" and gfpArgIndex = 1
      or
      this.getName() = "kmem_cache_alloc_node" and gfpArgIndex = 1
      or
      this.getName() = "__vmalloc" and gfpArgIndex = 1
      or
      this.getName() = "alloc_skb" and gfpArgIndex = 1
      or
      this.getName() = "dev_alloc_skb" and gfpArgIndex = 1
      or
      this.getName() = "__alloc_skb" and gfpArgIndex = 1
      or
      this.getName() = "alloc_pages" and gfpArgIndex = 0
      or
      this.getName() = "__get_free_pages" and gfpArgIndex = 0
    )
  }

  int getGfpArgIndex() { result = gfpArgIndex }
}

/** Expression evaluating to GFP_ATOMIC (directly or through obvious flag-ORs). */
predicate isGfpAtomicExpr(Expr e) {
  exists(MacroInvocation mi |
    mi.getMacroName() = "GFP_ATOMIC" and
    mi.getExpr() = e
  )
  or
  e.toString() = "GFP_ATOMIC"
  or
  // Conservative: any sub-expression mentions GFP_ATOMIC
  exists(MacroInvocation mi |
    mi.getMacroName() = "GFP_ATOMIC" and
    mi.getParentInvocation*().getExpr() = e
  )
}

/** Functions that strongly indicate the enclosing context may be atomic. */
predicate isAtomicMarker(FunctionCall fc) {
  exists(string n | n = fc.getTarget().getName() |
    n = "spin_lock" or
    n = "spin_lock_irq" or
    n = "spin_lock_irqsave" or
    n = "spin_lock_bh" or
    n = "_raw_spin_lock" or
    n = "_raw_spin_lock_irq" or
    n = "_raw_spin_lock_irqsave" or
    n = "_raw_spin_lock_bh" or
    n = "read_lock" or
    n = "read_lock_irq" or
    n = "read_lock_irqsave" or
    n = "read_lock_bh" or
    n = "write_lock" or
    n = "write_lock_irq" or
    n = "write_lock_irqsave" or
    n = "write_lock_bh" or
    n = "rcu_read_lock" or
    n = "rcu_read_lock_bh" or
    n = "rcu_read_lock_sched" or
    n = "preempt_disable" or
    n = "local_irq_disable" or
    n = "local_irq_save" or
    n = "local_bh_disable"
  )
}

/** Function whose name suggests it runs in interrupt / atomic context. */
predicate hasAtomicNamingHint(Function f) {
  exists(string n | n = f.getName() |
    n.matches("%_irq") or
    n.matches("%_isr") or
    n.matches("%_interrupt") or
    n.matches("%_handler") or
    n.matches("%_callback") or
    n.matches("%_tasklet") or
    n.matches("%_softirq") or
    n.matches("%_timer") or
    n.matches("%_napi%") or
    n.matches("%_poll") or
    n.matches("%_rx") or
    n.matches("%_tx") or
    n.matches("%_xmit%") or
    n.matches("%_notify%")
  )
}

/** Function appears to never run in atomic context: does not itself take a lock,
    is not named like an IRQ/handler, and is not called from such a function. */
predicate functionLikelyNonAtomic(Function f) {
  not exists(FunctionCall fc | fc.getEnclosingFunction() = f and isAtomicMarker(fc)) and
  not hasAtomicNamingHint(f) and
  not exists(Function caller, FunctionCall cc |
    cc.getTarget() = f and
    cc.getEnclosingFunction() = caller and
    (hasAtomicNamingHint(caller) or
     exists(FunctionCall fc2 | fc2.getEnclosingFunction() = caller and isAtomicMarker(fc2)))
  ) and
  // Hint: name suggests init/probe/setup/open — usually process context
  exists(string n | n = f.getName() |
    n.matches("%_init") or
    n.matches("%_init_%") or
    n.matches("init_%") or
    n.matches("%_probe") or
    n.matches("%_open") or
    n.matches("%_setup") or
    n.matches("%_create") or
    n.matches("%_alloc") or
    n.matches("%_register") or
    n.matches("%_start")
  )
}

from FunctionCall call, KernelAllocator alloc, Expr gfpArg, Function enclosing
where
  call.getTarget() = alloc and
  gfpArg = call.getArgument(alloc.getGfpArgIndex()) and
  isGfpAtomicExpr(gfpArg) and
  enclosing = call.getEnclosingFunction() and
  functionLikelyNonAtomic(enclosing)
select call,
  "Unnecessary GFP_ATOMIC in call to " + alloc.getName() +
    " inside non-atomic function '" + enclosing.getName() +
    "'; consider GFP_KERNEL."
