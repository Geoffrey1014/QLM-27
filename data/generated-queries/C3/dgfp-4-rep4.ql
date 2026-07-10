/**
 * @name delay-gfp: usb_submit_urb with GFP_ATOMIC in sleepable context
 * @description Flags calls to usb_submit_urb that pass GFP_ATOMIC while the
 *              call site is not inside a spinlock section and not guarded by
 *              an in_interrupt() check, i.e. the caller is in sleepable
 *              process context and GFP_KERNEL would be the correct choice.
 *              Mirrors commit 2453e60702e1 in drivers/media/usb/em28xx.
 * @kind problem
 * @problem.severity warning
 * @id qlm/delay-gfp-usb-submit-urb
 * @tags reliability
 *       performance
 */

import cpp

predicate isUsbSubmitCall(FunctionCall fc) {
  fc.getTarget().getName() = "usb_submit_urb"
}

predicate isGfpAtomicArg(FunctionCall fc) {
  fc.getArgument(1).getValue().toInt() = 32
}

predicate callIsInsideSpinlockSection(FunctionCall fc) {
  exists(FunctionCall lock |
    lock.getEnclosingFunction() = fc.getEnclosingFunction() and
    lock.getTarget().getName() in [
      "spin_lock", "spin_lock_irq", "spin_lock_irqsave", "spin_lock_bh"
    ] and
    lock.getLocation().getStartLine() < fc.getLocation().getStartLine() and
    not exists(FunctionCall unlock |
      unlock.getEnclosingFunction() = fc.getEnclosingFunction() and
      unlock.getTarget().getName() in [
        "spin_unlock", "spin_unlock_irq", "spin_unlock_irqrestore", "spin_unlock_bh"
      ] and
      unlock.getLocation().getStartLine() > lock.getLocation().getStartLine() and
      unlock.getLocation().getStartLine() < fc.getLocation().getStartLine()
    )
  )
}

predicate callIsGuardedByInInterrupt(FunctionCall fc) {
  exists(IfStmt ifs, FunctionCall inIrq |
    inIrq.getTarget().getName() = "in_interrupt" and
    ifs.getCondition().getAChild*() = inIrq and
    ifs.getThen().getAChild*() = fc.getEnclosingStmt()
  )
}

predicate isDelayGfpBug(FunctionCall fc) {
  isUsbSubmitCall(fc) and
  isGfpAtomicArg(fc) and
  not callIsInsideSpinlockSection(fc) and
  not callIsGuardedByInInterrupt(fc)
}

from FunctionCall fc
where isDelayGfpBug(fc)
select fc,
  "delay-gfp: usb_submit_urb with GFP_ATOMIC in sleepable context in $@",
  fc.getEnclosingFunction(), fc.getEnclosingFunction().getName()
