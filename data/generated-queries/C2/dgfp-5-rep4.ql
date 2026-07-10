/**
 * @name  rq3-c2-dgfp-5-rep4
 * @id    cpp/rq3/c2/dgfp-5-rep4
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects busy-wait delay calls (mdelay/udelay) in functions
 *              that run from non-atomic (workqueue/handler) context and
 *              should use usleep_range() instead.
 */
import cpp

predicate isBusyWaitDelay(FunctionCall fc) {
  fc.getTarget().getName() in ["mdelay", "udelay", "ndelay"]
}

predicate enclosingFunction(FunctionCall fc, Function f) {
  fc.getEnclosingFunction() = f
}

predicate noAtomicGuard(Function f) {
  not exists(FunctionCall lock |
    lock.getEnclosingFunction() = f and
    lock.getTarget().getName().regexpMatch("(spin_lock|spin_lock_irq|spin_lock_irqsave|spin_lock_bh|local_irq_disable|local_irq_save|preempt_disable|rcu_read_lock|raw_spin_lock|raw_spin_lock_irq|raw_spin_lock_irqsave)")
  )
}

predicate calledFromWorkqueue(Function f) {
  f.getName().regexpMatch(".*_(work|handler|worker|cmd_handler|task|thread)") or
  exists(Function caller |
    exists(FunctionCall fc | fc.getTarget() = f and fc.getEnclosingFunction() = caller) and
    caller.getName().regexpMatch(".*_(work|handler|worker|cmd_handler|task|thread)")
  )
}

from FunctionCall fc, Function f
where
  isBusyWaitDelay(fc) and
  enclosingFunction(fc, f) and
  noAtomicGuard(f) and
  calledFromWorkqueue(f)
select fc, "Busy-wait delay (" + fc.getTarget().getName() + ") in non-atomic workqueue/handler context; consider usleep_range()."
