/**
 * @name  usb_submit_urb() with GFP_ATOMIC in sleepable init/start context (delay-gfp) [L0]
 * @id    cpp/rq3/l0/dgfp-4-rep5
 * @kind  problem
 * @problem.severity warning
 * @description Zero-shot compositional (L0) query for RQ4 delay-gfp
 *              pattern. A single helper predicate identifies
 *              `usb_submit_urb(..., GFP_ATOMIC)` call sites; the
 *              assembly where-clause inlines the sleepable-context
 *              filter (init/probe/resume/suspend/start_streaming/
 *              start_feed/open/xfer/setup/start) and excludes atomic
 *              contexts (irq/isr/interrupt/tasklet/atomic) plus any
 *              function that acquires a spinlock, disables IRQ/preempt,
 *              or enters an RCU read side before the submit site.
 *              Seed: 2453e60702e1 (em28xx_init_usb_xfer).
 * @tags reliability
 *       delay-gfp
 *       performance
 */

import cpp

predicate isAtomicUsbSubmit(FunctionCall fc) {
  fc.getTarget().getName() = "usb_submit_urb" and
  exists(int v | v = fc.getArgument(1).getValue().toInt() | v = 32)
}

from FunctionCall fc, Function enc
where
  isAtomicUsbSubmit(fc) and
  enc = fc.getEnclosingFunction() and
  (
    enc.getName().matches("%_init_%") or
    enc.getName().matches("%_init") or
    enc.getName().matches("%init_%") or
    enc.getName().matches("%_probe%") or
    enc.getName().matches("%_resume%") or
    enc.getName().matches("%_suspend%") or
    enc.getName().matches("%start_streaming%") or
    enc.getName().matches("%start_feed%") or
    enc.getName().matches("%_open%") or
    enc.getName().matches("%_xfer%") or
    enc.getName().matches("%_setup%") or
    enc.getName().matches("%_start%")
  ) and
  not (
    enc.getName().matches("%_irq_handler%") or
    enc.getName().matches("%_isr%") or
    enc.getName().matches("%_interrupt%") or
    enc.getName().matches("%irq_handler%") or
    enc.getName().matches("%tasklet%") or
    enc.getName().matches("%_atomic%")
  ) and
  not exists(FunctionCall lockCall |
    lockCall.getEnclosingFunction() = enc and
    (
      lockCall.getTarget().getName() = "spin_lock" or
      lockCall.getTarget().getName() = "spin_lock_irq" or
      lockCall.getTarget().getName() = "spin_lock_irqsave" or
      lockCall.getTarget().getName() = "spin_lock_bh" or
      lockCall.getTarget().getName() = "local_irq_save" or
      lockCall.getTarget().getName() = "local_irq_disable" or
      lockCall.getTarget().getName() = "preempt_disable" or
      lockCall.getTarget().getName() = "rcu_read_lock"
    ) and
    lockCall.getLocation().getStartLine() < fc.getLocation().getStartLine()
  )
select fc,
  "usb_submit_urb() called with GFP_ATOMIC in a sleepable init/start context '" +
  enc.getName() +
  "'; consider GFP_KERNEL."
