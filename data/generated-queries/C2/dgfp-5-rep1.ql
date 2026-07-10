/**
 * @name  rq3-c2-dgfp-5-rep1
 * @id    cpp/rq3/c2/dgfp-5-rep1
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Flags mdelay()/udelay() busy-wait calls in sleepable
 *              (process/workqueue) context, where usleep_range() should
 *              be used instead.
 */

import cpp

predicate isBusyWaitCall(FunctionCall fc) {
  exists(Function callee | callee = fc.getTarget() |
    callee.getName() = "mdelay" or
    callee.getName() = "udelay" or
    callee.getName() = "ndelay" or
    callee.getName() = "__const_udelay" or
    callee.getName() = "__udelay"
  )
}

predicate isAtomicEntryFunction(Function f) {
  f.getName().matches("%_irq_handler") or
  f.getName().matches("%_isr") or
  f.getName().matches("%_interrupt") or
  exists(FunctionCall fc |
    fc.getEnclosingFunction() = f and
    (
      fc.getTarget().getName() = "spin_lock" or
      fc.getTarget().getName() = "spin_lock_irq" or
      fc.getTarget().getName() = "spin_lock_irqsave" or
      fc.getTarget().getName() = "spin_lock_bh" or
      fc.getTarget().getName() = "local_irq_disable" or
      fc.getTarget().getName() = "preempt_disable" or
      fc.getTarget().getName() = "rcu_read_lock"
    )
  )
}

predicate isWorkqueueHandler(Function f) {
  exists(FunctionAccess fa |
    fa.getTarget() = f and
    exists(MacroInvocation mi |
      mi.getMacroName() in [
        "INIT_WORK", "INIT_DELAYED_WORK", "DECLARE_WORK", "DECLARE_DELAYED_WORK",
        "INIT_WORK_ONSTACK", "INIT_DELAYED_WORK_ONSTACK"
      ] and
      fa.getLocation().getStartLine() = mi.getLocation().getStartLine() and
      fa.getFile() = mi.getFile()
    )
  )
  or
  f.getType() instanceof VoidType and
  f.getNumberOfParameters() = 1 and
  exists(Parameter p |
    p = f.getParameter(0) and
    p.getType().getName().matches("%work_struct%")
  )
}

predicate calledFromSleepableContext(Function f) {
  not isAtomicEntryFunction(f) and
  (
    isWorkqueueHandler(f)
    or
    exists(Function caller |
      calledFromSleepableContext(caller) and
      not isAtomicEntryFunction(caller) and
      exists(FunctionCall fc |
        fc.getEnclosingFunction() = caller and
        fc.getTarget() = f
      )
    )
  )
}

predicate busyWaitInSleepableContext(FunctionCall fc) {
  isBusyWaitCall(fc) and
  calledFromSleepableContext(fc.getEnclosingFunction())
}

from FunctionCall fc
where busyWaitInSleepableContext(fc)
select fc, "mdelay()/udelay() busy-wait in a sleepable (workqueue/process) context; consider usleep_range()."
