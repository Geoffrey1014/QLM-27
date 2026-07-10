/**
 * @name  rq3-l0-dgfp-4-rep1
 * @id    cpp/rq3/l0/dgfp-4-rep1
 * @kind  problem
 * @problem.severity warning
 * @description Zero-shot compositional (L0) query for RQ4 delay-gfp pattern
 *              (GFP-flag sub-variant). Flags calls that pass a GFP_ATOMIC
 *              (value 0x20 = 32) flag argument to a well-known kernel
 *              allocator / submission API while the enclosing function's
 *              name shape indicates a sleepable context (streaming-init,
 *              probe, start-streaming, resume, suspend, open, release,
 *              ioctl) and no spinlock/preempt/RCU/IRQ-disable primitive
 *              is present in that function. Single predicate + assembly;
 *              no per-predicate refine, no assemble-refine.
 *              Seed: 2453e60702e1 (media: usb: em28xx: em28xx_init_usb_xfer).
 */

import cpp

predicate isGfpAtomicInSleepableContext(FunctionCall fc) {
  (
    fc.getTarget().getName() = "usb_submit_urb" or
    fc.getTarget().getName() = "kmalloc" or
    fc.getTarget().getName() = "kzalloc" or
    fc.getTarget().getName() = "kcalloc" or
    fc.getTarget().getName() = "krealloc" or
    fc.getTarget().getName() = "vmalloc" or
    fc.getTarget().getName() = "alloc_skb" or
    fc.getTarget().getName() = "__alloc_skb" or
    fc.getTarget().getName() = "skb_copy" or
    fc.getTarget().getName() = "kmem_cache_alloc"
  )
  and exists(Expr flag |
    flag = fc.getAnArgument() and
    flag.getValue().toInt() = 32
  )
  and exists(Function enclosing | enclosing = fc.getEnclosingFunction() |
    (
      enclosing.getName().matches("%_init_usb_xfer%") or
      enclosing.getName().matches("%_probe%") or
      enclosing.getName().matches("%_start_streaming%") or
      enclosing.getName().matches("%_start_feed%") or
      enclosing.getName().matches("%_resume%") or
      enclosing.getName().matches("%_suspend%") or
      enclosing.getName().matches("%_open%") or
      enclosing.getName().matches("%_release%") or
      enclosing.getName().matches("%_ioctl%")
    )
    and not enclosing.getName().matches("%_irq_handler%")
    and not enclosing.getName().matches("%_isr%")
    and not enclosing.getName().matches("%_interrupt%")
    and not enclosing.getName().matches("%_tasklet%")
    and not enclosing.getName().matches("%_softirq%")
    and not exists(FunctionCall lockfc |
      lockfc.getEnclosingFunction() = enclosing and
      (
        lockfc.getTarget().getName() = "spin_lock" or
        lockfc.getTarget().getName() = "spin_lock_irq" or
        lockfc.getTarget().getName() = "spin_lock_irqsave" or
        lockfc.getTarget().getName() = "spin_lock_bh" or
        lockfc.getTarget().getName() = "local_irq_disable" or
        lockfc.getTarget().getName() = "preempt_disable" or
        lockfc.getTarget().getName() = "rcu_read_lock"
      )
    )
  )
}

from FunctionCall fc
where isGfpAtomicInSleepableContext(fc)
select fc,
  "GFP_ATOMIC allocation/submission in a sleepable context (probe/init/start-streaming/resume/suspend/open/release/ioctl); consider GFP_KERNEL."
