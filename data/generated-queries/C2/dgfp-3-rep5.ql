/**
 * @name  rq3-c2-dgfp-3-rep5
 * @id    cpp/rq3/c2/dgfp-3-rep5
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2 (delay-gfp pattern).
 */
import cpp

/**
 * Holds if `name` is a kernel memory allocator that takes a gfp_t flag argument.
 */
predicate isGfpAllocatorName(string name) {
  name = "kmalloc" or
  name = "kzalloc" or
  name = "kcalloc" or
  name = "kmalloc_array" or
  name = "krealloc" or
  name = "kmemdup" or
  name = "kstrdup" or
  name = "vmalloc" or
  name = "vzalloc" or
  name = "kvmalloc" or
  name = "kvzalloc" or
  name = "alloc_skb" or
  name = "__alloc_skb" or
  name = "kmem_cache_alloc"
}

/**
 * Holds if `fc` is a call to a gfp allocator and `flagArg` is the gfp flag argument.
 */
predicate isGfpAllocCall(FunctionCall fc, Expr flagArg) {
  exists(string n |
    isGfpAllocatorName(n) and
    fc.getTarget().getName() = n
  ) and
  (
    // Most allocators take gfp as the last argument
    flagArg = fc.getArgument(fc.getNumberOfArguments() - 1)
  )
}

/**
 * Holds if `flagArg` syntactically refers to GFP_ATOMIC.
 */
predicate isGfpAtomic(Expr flagArg) {
  exists(string s | s = flagArg.toString() | s.matches("%GFP_ATOMIC%"))
  or
  exists(MacroInvocation mi |
    mi.getMacroName() = "GFP_ATOMIC" and
    mi.getExpr() = flagArg
  )
  or
  exists(MacroInvocation mi |
    mi.getMacroName() = "GFP_ATOMIC" and
    mi.getParentInvocation*().getExpr() = flagArg
  )
}

/**
 * Holds if `f` is a function whose name suggests it runs only in process/init
 * context (not atomic). Heuristic: init/probe/open/setup/create functions.
 */
predicate isProcessContextFunction(Function f) {
  exists(string n | n = f.getName() |
    n.matches("%_init") or
    n.matches("%_probe") or
    n.matches("%_open") or
    n.matches("%_setup") or
    n.matches("%_create") or
    n.matches("%_register") or
    n.matches("%_alloc") or
    n.matches("init_%") or
    n.matches("probe_%") or
    n.matches("setup_%")
  )
}

/**
 * Holds if `fc` is a GFP_ATOMIC allocation call inside a function that
 * appears to run only in process context (so GFP_ATOMIC is unnecessary).
 */
predicate suspiciousAtomicAlloc(FunctionCall fc) {
  exists(Expr flag |
    isGfpAllocCall(fc, flag) and
    isGfpAtomic(flag) and
    isProcessContextFunction(fc.getEnclosingFunction())
  )
}

from FunctionCall fc
where suspiciousAtomicAlloc(fc)
select fc,
  "Allocation with GFP_ATOMIC in function '" + fc.getEnclosingFunction().getName() +
    "' which appears to run only in process context; consider GFP_KERNEL."
