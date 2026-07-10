/**
 * @name  rq3-c2-dgfp-5-rep3
 * @id    cpp/rq3/c2/dgfp-5-rep3
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Flags mdelay()/udelay() busy-wait calls that appear in functions
 *              reachable from sleepable (workqueue / file_operations / ioctl)
 *              entry points and not guarded by a spinlock, suggesting that a
 *              sleeping delay (usleep_range/msleep) would be more appropriate.
 */

import cpp

predicate isBusyWaitDelayCall(FunctionCall fc) {
  exists(Function f | f = fc.getTarget() |
    f.getName() = "mdelay" or
    f.getName() = "udelay" or
    f.getName() = "ndelay" or
    f.getName() = "__udelay" or
    f.getName() = "__mdelay" or
    f.getName() = "__const_udelay"
  )
}

predicate isAtomicContextFunction(Function f) {
  // Functions whose names suggest they always run in atomic context.
  exists(string n | n = f.getName() |
    n.matches("%_irq%") or
    n.matches("%_isr%") or
    n.matches("%interrupt_handler%") or
    n.matches("%_handler") and n.matches("%irq%") or
    n.matches("%tasklet%") or
    n.matches("%softirq%") or
    n.matches("%_atomic%") or
    n.matches("%spin_lock%")
  )
}

predicate isWorkqueueOrSleepableEntry(Function f) {
  // Function is registered as a workqueue handler or other clearly-sleepable
  // entry: it is taken as the second argument of INIT_WORK / INIT_DELAYED_WORK,
  // or it appears as a member of file_operations / similar process-context
  // dispatch tables. We approximate by looking at how f is used as an
  // initializer / function-pointer assignment.
  exists(FunctionAccess fa | fa.getTarget() = f |
    // Used as initializer for a struct field that suggests sleepable context.
    exists(Initializer init | init.getExpr().getAChild*() = fa) or
    // Address-of taken anywhere (broad heuristic; combined with negative
    // signals below).
    exists(AddressOfExpr a | a.getOperand() = fa)
  )
  or
  // Name-based fallback: handlers/callbacks frequently associated with
  // sleepable kernel contexts.
  exists(string n | n = f.getName() |
    n.matches("%_work%") or
    n.matches("%_worker") or
    n.matches("%_workfn") or
    n.matches("%_cmd_handler%") or
    n.matches("%_thread%") or
    n.matches("%_probe") or
    n.matches("%_open") or
    n.matches("%_release") or
    n.matches("%_read") or
    n.matches("%_write") or
    n.matches("%_ioctl") or
    n.matches("%_show") or
    n.matches("%_store")
  )
}

predicate holdsSpinlockBefore(FunctionCall fc) {
  // Approximation: there exists, in the same enclosing function, a call to a
  // spinlock acquire that lexically precedes fc and no matching release
  // between them on the same line range. We use a simple lexical check by
  // location ordering within the same function.
  exists(FunctionCall lock, Function enclosing |
    enclosing = fc.getEnclosingFunction() and
    lock.getEnclosingFunction() = enclosing and
    (
      lock.getTarget().getName().matches("spin_lock%") or
      lock.getTarget().getName().matches("raw_spin_lock%") or
      lock.getTarget().getName().matches("read_lock%") or
      lock.getTarget().getName().matches("write_lock%") or
      lock.getTarget().getName() = "local_irq_save" or
      lock.getTarget().getName() = "local_irq_disable" or
      lock.getTarget().getName() = "preempt_disable" or
      lock.getTarget().getName() = "rcu_read_lock"
    ) and
    lock.getLocation().getStartLine() < fc.getLocation().getStartLine() and
    not exists(FunctionCall unlock |
      unlock.getEnclosingFunction() = enclosing and
      (
        unlock.getTarget().getName().matches("spin_unlock%") or
        unlock.getTarget().getName().matches("raw_spin_unlock%") or
        unlock.getTarget().getName().matches("read_unlock%") or
        unlock.getTarget().getName().matches("write_unlock%") or
        unlock.getTarget().getName() = "local_irq_restore" or
        unlock.getTarget().getName() = "local_irq_enable" or
        unlock.getTarget().getName() = "preempt_enable" or
        unlock.getTarget().getName() = "rcu_read_unlock"
      ) and
      unlock.getLocation().getStartLine() > lock.getLocation().getStartLine() and
      unlock.getLocation().getStartLine() < fc.getLocation().getStartLine()
    )
  )
}

predicate delayMillisecondsArg(FunctionCall fc, int ms) {
  isBusyWaitDelayCall(fc) and
  exists(Expr arg | arg = fc.getArgument(0) |
    ms = arg.getValue().toInt()
  )
}

predicate isMisusedBusyWait(FunctionCall fc) {
  isBusyWaitDelayCall(fc) and
  exists(Function enclosing | enclosing = fc.getEnclosingFunction() |
    isWorkqueueOrSleepableEntry(enclosing) and
    not isAtomicContextFunction(enclosing)
  ) and
  not holdsSpinlockBefore(fc) and
  // Prefer mdelay or udelay/mdelay-equivalent of at least 1ms (>=1000us) as
  // these are the canonical "should have slept" cases.
  (
    fc.getTarget().getName() = "mdelay" or
    fc.getTarget().getName() = "__mdelay" or
    exists(int ms | delayMillisecondsArg(fc, ms) and ms >= 1)
  )
}

from FunctionCall fc
where isMisusedBusyWait(fc)
select fc, "mdelay()/udelay() busy-waits in a likely sleepable context; consider usleep_range()/msleep()."
