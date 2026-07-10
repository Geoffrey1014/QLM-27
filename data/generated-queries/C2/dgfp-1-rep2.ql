/**
 * @name  rq3-c2-dgfp-1-rep2
 * @id    cpp/rq3/c2/dgfp-1-rep2
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects mdelay() called in a sleepable context (e.g. resume/suspend/probe)
 *              where msleep() would be appropriate.
 */
import cpp

predicate isMdelayCall(FunctionCall fc) {
  fc.getTarget().getName() = "mdelay"
}

predicate isSleepableContextFunction(Function f) {
  exists(string n | n = f.getName() |
    n.matches("%_resume") or
    n.matches("%_suspend") or
    n.matches("%_probe") or
    n.matches("%_remove") or
    n.matches("%_init") or
    n.matches("%_shutdown") or
    n = "resume" or n = "suspend" or n = "probe"
  )
}

predicate mdelayInSleepableContext(FunctionCall fc, Function f) {
  isMdelayCall(fc) and
  fc.getEnclosingFunction() = f and
  isSleepableContextFunction(f)
}

predicate noAtomicGuardBefore(FunctionCall fc) {
  not exists(FunctionCall lock |
    lock.getEnclosingFunction() = fc.getEnclosingFunction() and
    (
      lock.getTarget().getName().matches("spin_lock%") or
      lock.getTarget().getName().matches("raw_spin_lock%") or
      lock.getTarget().getName() = "local_irq_disable" or
      lock.getTarget().getName() = "preempt_disable" or
      lock.getTarget().getName() = "rcu_read_lock"
    )
  )
}

from FunctionCall fc, Function f
where mdelayInSleepableContext(fc, f) and noAtomicGuardBefore(fc)
select fc, "mdelay() called in sleepable context " + f.getName() + "; consider msleep()."
