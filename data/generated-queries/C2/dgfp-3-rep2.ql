/**
 * @name  rq3-c2-dgfp-3-rep2
 * @id    cpp/rq3/c2/dgfp-3-rep2
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2 (delay-gfp pattern).
 */
import cpp

/* Predicate: the call is an allocation taking a gfp_t flag */
predicate isGfpAllocCall(FunctionCall fc, Expr gfpArg) {
  exists(string n | n = fc.getTarget().getName() |
    n = "kmalloc" or n = "kzalloc" or n = "kcalloc" or n = "krealloc" or
    n = "kmalloc_array" or n = "kmemdup" or n = "kstrdup" or n = "kstrndup" or
    n = "vmalloc" or n = "kvmalloc" or n = "kvzalloc" or
    n = "alloc_skb" or n = "__alloc_skb" or n = "dev_alloc_skb" or
    n = "alloc_pages" or n = "__get_free_pages" or n = "get_zeroed_page" or
    n = "kmem_cache_alloc" or n = "kmem_cache_zalloc" or n = "mempool_alloc"
  ) and
  gfpArg = fc.getAnArgument() and
  gfpArg.getType().getName().matches("%gfp_t%")
}

/* Predicate: the gfp argument is GFP_ATOMIC */
predicate isGfpAtomic(Expr gfpArg) {
  exists(MacroInvocation mi |
    mi.getMacroName() = "GFP_ATOMIC" and
    mi.getExpr() = gfpArg
  )
  or
  gfpArg.toString() = "GFP_ATOMIC"
}

/* Predicate: the enclosing function looks like an init / setup / probe (non-atomic) */
predicate inNonAtomicLikelyFunction(FunctionCall fc) {
  exists(Function f | f = fc.getEnclosingFunction() |
    f.getName().matches("%_init") or
    f.getName().matches("%_init_%") or
    f.getName().matches("init_%") or
    f.getName().matches("%_probe") or
    f.getName().matches("%_setup") or
    f.getName().matches("%_open") or
    f.getName().matches("%_create") or
    f.getName().matches("%_alloc") or
    f.getName().matches("%_register")
  )
}

/* Predicate: the function does NOT obviously run in atomic context.
 * Approximation: it does not call any spin_lock / local_irq_disable / rcu_read_lock
 * before the allocation in the same function. */
predicate notInAtomicContext(FunctionCall fc) {
  not exists(FunctionCall lockCall, Function enc |
    enc = fc.getEnclosingFunction() and
    lockCall.getEnclosingFunction() = enc and
    lockCall.getLocation().getStartLine() < fc.getLocation().getStartLine() and
    exists(string ln | ln = lockCall.getTarget().getName() |
      ln.matches("spin_lock%") or
      ln.matches("raw_spin_lock%") or
      ln.matches("read_lock%") or
      ln.matches("write_lock%") or
      ln = "local_irq_disable" or
      ln = "local_irq_save" or
      ln = "preempt_disable" or
      ln = "rcu_read_lock" or
      ln = "rcu_read_lock_bh" or
      ln = "rcu_read_lock_sched"
    )
  )
}

from FunctionCall fc, Expr gfpArg
where
  isGfpAllocCall(fc, gfpArg) and
  isGfpAtomic(gfpArg) and
  inNonAtomicLikelyFunction(fc) and
  notInAtomicContext(fc)
select fc, "delay-gfp: GFP_ATOMIC used in likely non-atomic context (consider GFP_KERNEL)"
