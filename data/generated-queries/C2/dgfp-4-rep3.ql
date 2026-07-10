/**
 * @name  rq3-c2-dgfp-4-rep3
 * @id    cpp/rq3/c2/dgfp-4-rep3
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects USB/allocation APIs invoked with GFP_ATOMIC inside
 *              functions that run only in sleepable context (probe/init/
 *              open/start/configure/resume/suspend/remove), where GFP_KERNEL
 *              should be used instead (delay-gfp / DCNS pattern).
 */

import cpp

predicate isAllocLikeApi(string name) {
  name = "usb_submit_urb" or
  name = "usb_alloc_urb" or
  name = "kmalloc" or
  name = "kzalloc" or
  name = "kcalloc" or
  name = "krealloc" or
  name = "kmem_cache_alloc" or
  name = "alloc_skb" or
  name = "__alloc_skb" or
  name = "dev_alloc_skb" or
  name = "netdev_alloc_skb"
}

predicate usesGfpAtomic(FunctionCall fc) {
  isAllocLikeApi(fc.getTarget().getName()) and
  exists(Expr arg, int i |
    i in [0 .. fc.getNumberOfArguments() - 1] and
    arg = fc.getArgument(i) and
    arg.toString().matches("%GFP_ATOMIC%")
  )
}

predicate isSleepableContext(Function f) {
  exists(string n | n = f.getName() |
    n.matches("%_probe") or
    n.matches("%_init") or
    n.matches("%_open") or
    n.matches("%_release") or
    n.matches("%_remove") or
    n.matches("%_resume") or
    n.matches("%_suspend") or
    n.matches("%_start") or
    n.matches("%_configure") or
    n.matches("%init_usb_xfer%") or
    n.matches("%_setup")
  )
}

predicate gfpAtomicInSleepable(FunctionCall fc, Function f) {
  usesGfpAtomic(fc) and
  isSleepableContext(f) and
  fc.getEnclosingFunction() = f
}

from FunctionCall fc, Function f
where gfpAtomicInSleepable(fc, f)
select fc, "GFP_ATOMIC used in sleepable-context function '" + f.getName() + "'; consider GFP_KERNEL."
