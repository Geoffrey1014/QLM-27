/**
 * @name Sleep in atomic context (v4: depth-2 interprocedural)
 * @description Detects sleeping functions called within atomic context,
 *              following call chains up to depth 2. This matches the
 *              f3691e00 pattern: lock -> call -> call -> sleep.
 * @kind problem
 * @problem.severity error
 * @id cpp/sleep-in-atomic-context-v4
 */

import cpp

predicate isAtomicEntry(FunctionCall fc) {
  fc.getTarget().getName().matches("%spin_lock%")
  or fc.getTarget().getName().matches("%read_lock%")
  or fc.getTarget().getName().matches("%write_lock%")
  or fc.getTarget().getName() = "preempt_disable"
  or fc.getTarget().getName() = "local_irq_disable"
  or fc.getTarget().getName() = "rcu_read_lock"
}

predicate isAtomicExit(FunctionCall fc) {
  fc.getTarget().getName().matches("%spin_unlock%")
  or fc.getTarget().getName().matches("%read_unlock%")
  or fc.getTarget().getName().matches("%write_unlock%")
  or fc.getTarget().getName() = "preempt_enable"
  or fc.getTarget().getName() = "local_irq_enable"
  or fc.getTarget().getName() = "rcu_read_unlock"
}

predicate isSleepingFunction(Function f) {
  f.getName() = "usleep_range"
  or f.getName() = "msleep"
  or f.getName() = "ssleep"
  or f.getName() = "schedule"
  or f.getName() = "schedule_timeout"
  or f.getName().matches("wait_event%")
  or f.getName() = "mutex_lock"
}

predicate isMatchingLockPair(FunctionCall lock, FunctionCall unlock) {
  exists(string lockName, string unlockName |
    lockName = lock.getTarget().getName() and
    unlockName = unlock.getTarget().getName() |
    lockName = "spin_lock" and unlockName = "spin_unlock"
    or lockName = "spin_lock_bh" and unlockName = "spin_unlock_bh"
    or lockName = "spin_lock_irq" and unlockName = "spin_unlock_irq"
    or lockName = "spin_lock_irqsave" and unlockName = "spin_unlock_irqrestore"
    or lockName = "read_lock" and unlockName = "read_unlock"
    or lockName = "write_lock" and unlockName = "write_unlock"
    or lockName = "write_lock_irqsave" and unlockName = "write_unlock_irqrestore"
    or lockName = "preempt_disable" and unlockName = "preempt_enable"
    or lockName = "local_irq_disable" and unlockName = "local_irq_enable"
    or lockName = "rcu_read_lock" and unlockName = "rcu_read_unlock"
  )
}

/**
 * Recursive predicate: function f transitively calls a sleeping function
 * at the given depth. Tracks the entire call chain for reporting.
 *
 * depth=0: f directly calls a sleeping function
 * depth=1: f calls g, and g directly calls a sleeping function
 * depth=2: f calls g, g calls h, and h directly calls a sleeping function
 */
predicate callsSleeperTransitively(Function f, string callChain, int depth) {
  // Base case: f directly contains a call to a sleeping function
  depth = 0 and
  exists(FunctionCall fc |
    fc.getEnclosingFunction() = f and
    isSleepingFunction(fc.getTarget()) and
    callChain = fc.getTarget().getName() + "()"
  )
  or
  // Recursive case depth 1
  depth = 1 and
  exists(FunctionCall fc, string innerChain |
    fc.getEnclosingFunction() = f and
    not isSleepingFunction(fc.getTarget()) and
    callsSleeperTransitively(fc.getTarget(), innerChain, 0) and
    callChain = fc.getTarget().getName() + "() -> " + innerChain
  )
  or
  // Recursive case depth 2
  depth = 2 and
  exists(FunctionCall fc, string innerChain |
    fc.getEnclosingFunction() = f and
    not isSleepingFunction(fc.getTarget()) and
    callsSleeperTransitively(fc.getTarget(), innerChain, 1) and
    callChain = fc.getTarget().getName() + "() -> " + innerChain
  )
}

from
  FunctionCall lockCall, FunctionCall callInAtomicRegion,
  FunctionCall unlockCall, string callChain, int depth
where
  isAtomicEntry(lockCall) and
  isAtomicExit(unlockCall) and
  isMatchingLockPair(lockCall, unlockCall) and
  lockCall.getEnclosingFunction() = unlockCall.getEnclosingFunction() and
  callInAtomicRegion.getEnclosingFunction() = lockCall.getEnclosingFunction() and
  lockCall.getLocation().getStartLine() < callInAtomicRegion.getLocation().getStartLine() and
  callInAtomicRegion.getLocation().getStartLine() < unlockCall.getLocation().getStartLine() and
  (
    // Direct sleeping call in atomic region
    (
      isSleepingFunction(callInAtomicRegion.getTarget()) and
      callChain = callInAtomicRegion.getTarget().getName() + "()" and
      depth = 0
    )
    or
    // Transitive call to sleeping function
    (
      not isSleepingFunction(callInAtomicRegion.getTarget()) and
      callsSleeperTransitively(callInAtomicRegion.getTarget(), callChain, depth) and
      depth in [0 .. 2]
    )
  )
select callInAtomicRegion,
  "Call to '" + callInAtomicRegion.getTarget().getName() +
  "' in atomic context (between $@ / $@) leads to sleeping: " + callChain +
  " [depth=" + depth.toString() + "]",
  lockCall, lockCall.getTarget().getName(),
  unlockCall, unlockCall.getTarget().getName()
