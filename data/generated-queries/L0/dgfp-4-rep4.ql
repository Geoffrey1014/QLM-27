/**
 * @name  GFP_ATOMIC passed to usb_submit_urb in sleepable context (delay-gfp) [L0]
 * @description Detects usb_submit_urb() call sites that pass GFP_ATOMIC
 *              (integer literal 32 after preprocessing) inside a
 *              streaming/init/probe/resume flavoured enclosing function
 *              when the enclosing function is not named like an atomic
 *              context (IRQ handler / ISR / interrupt) and does not
 *              acquire a spinlock or disable IRQs/preemption/RCU before
 *              the submit site. Such calls should pass GFP_KERNEL
 *              because the caller chain reaches the submit from process
 *              context. Pattern from commit 2453e60702e1 ("media: usb:
 *              em28xx: Replace GFP_ATOMIC with GFP_KERNEL in
 *              em28xx_init_usb_xfer()").
 *
 *              L0 zero-shot variant: exactly one helper predicate
 *              (isAtomicUsbSubmit); sleepable-name / atomic-name /
 *              lock-held tests are inlined in the assembly where-clause.
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3/l0/delay-gfp-atomic-usb-submit-in-init
 * @tags reliability
 *       delay-gfp
 *       performance
 */

import cpp

predicate isAtomicUsbSubmit(FunctionCall fc) {
  fc.getTarget().getName() = "usb_submit_urb" and
  fc.getArgument(1).getValue() = "32"
}

from FunctionCall alloc, Function enc
where
  isAtomicUsbSubmit(alloc) and
  enc = alloc.getEnclosingFunction() and
  (enc.getName().matches("%_init%") or
   enc.getName().matches("%_probe%") or
   enc.getName().matches("%_start%") or
   enc.getName().matches("%start_%") or
   enc.getName().matches("%_setup%") or
   enc.getName().matches("%_resume%") or
   enc.getName().matches("%_prepare%") or
   enc.getName().matches("%_xfer%") or
   enc.getName().matches("%_streaming%")) and
  not (enc.getName().matches("%_isr%") or
       enc.getName().matches("%_irq_handler%") or
       enc.getName().matches("%_interrupt%") or
       enc.getName().matches("%irq_handler%") or
       enc.getName().matches("%_irq") or
       enc.getName().matches("%_irq_%")) and
  not exists(FunctionCall lockCall |
    lockCall.getEnclosingFunction() = enc and
    (lockCall.getTarget().getName() = "spin_lock" or
     lockCall.getTarget().getName() = "spin_lock_irq" or
     lockCall.getTarget().getName() = "spin_lock_irqsave" or
     lockCall.getTarget().getName() = "spin_lock_bh" or
     lockCall.getTarget().getName() = "local_irq_save" or
     lockCall.getTarget().getName() = "local_irq_disable" or
     lockCall.getTarget().getName() = "preempt_disable" or
     lockCall.getTarget().getName() = "rcu_read_lock") and
    lockCall.getLocation().getStartLine() < alloc.getLocation().getStartLine()
  )
select alloc,
  "GFP_ATOMIC passed to usb_submit_urb in sleepable init/start context '" +
    enc.getName() +
    "'; caller chain is process context, so GFP_KERNEL is appropriate."
