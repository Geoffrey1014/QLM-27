/**
 * @name  rq3-c2-dgfp-4-rep5
 * @id    cpp/rq3/c2/dgfp-4-rep5
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2 (delay-gfp).
 */
import cpp

/* isGfpAtomicArg: identifies an argument expression that is the GFP_ATOMIC macro. */
predicate isGfpAtomicArg(Expr arg) {
  exists(MacroInvocation mi |
    mi.getMacroName() = "GFP_ATOMIC" and
    mi.getExpr() = arg
  )
}

/* callPassesGfpAtomic: a function call passes GFP_ATOMIC as one of its arguments. */
predicate callPassesGfpAtomic(FunctionCall fc, Expr gfpArg) {
  gfpArg = fc.getAnArgument() and
  isGfpAtomicArg(gfpArg)
}

/* isAllocOrSubmitApi: target API names that take a GFP flag. */
predicate isAllocOrSubmitApi(Function f) {
  f.getName() in [
    "usb_submit_urb", "kmalloc", "kzalloc", "kcalloc", "krealloc",
    "kmem_cache_alloc", "alloc_skb", "__alloc_skb", "vmalloc", "vzalloc",
    "kmalloc_array", "kmemdup", "kstrdup", "kstrndup"
  ]
}

/* callsBlockingApi: function body contains a call to a known-blocking API. */
predicate callsBlockingApi(Function f) {
  exists(FunctionCall c | c.getEnclosingFunction() = f |
    c.getTarget().getName() in [
      "msleep", "usleep_range", "ssleep", "schedule", "schedule_timeout",
      "mutex_lock", "mutex_lock_interruptible", "down", "down_interruptible",
      "wait_event", "wait_event_interruptible", "wait_for_completion",
      "kmalloc", "kzalloc"
    ]
  )
}

/* enclosingFunctionMayBlock: the function enclosing fc itself may sleep
 * (i.e. is NOT plausibly an atomic-context handler). Heuristic: it calls
 * a known-blocking API somewhere in its body, AND its name does NOT suggest
 * an IRQ handler. */
predicate enclosingFunctionMayBlock(FunctionCall fc) {
  exists(Function f |
    f = fc.getEnclosingFunction() and
    callsBlockingApi(f) and
    not f.getName().toLowerCase().matches("%irq%") and
    not f.getName().toLowerCase().matches("%isr%") and
    not f.getName().toLowerCase().matches("%_atomic%")
  )
}

/* suspiciousGfpAtomic: an allocation/submission call passes GFP_ATOMIC but
 * is inside a function that appears to be non-atomic. */
predicate suspiciousGfpAtomic(FunctionCall fc, Expr gfpArg) {
  callPassesGfpAtomic(fc, gfpArg) and
  isAllocOrSubmitApi(fc.getTarget()) and
  enclosingFunctionMayBlock(fc)
}

from FunctionCall fc, Expr gfpArg
where suspiciousGfpAtomic(fc, gfpArg)
select fc, "Call to " + fc.getTarget().getName() +
  " uses GFP_ATOMIC but enclosing function may sleep; consider GFP_KERNEL."
