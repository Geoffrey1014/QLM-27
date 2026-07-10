/**
 * @name Busy-wait mdelay/udelay in non-atomic context
 * @description Detects calls to busy-wait delay primitives (mdelay, udelay, ndelay)
 *              that occur in functions never invoked from atomic context. These
 *              should be replaced with sleeping equivalents (msleep, usleep_range)
 *              to avoid wasting CPU cycles.
 * @kind problem
 * @problem.severity warning
 * @id cpp/busy-wait-in-non-atomic
 * @tags efficiency
 *       correctness
 */

import cpp
import semmle.code.cpp.controlflow.IRGuards

/**
 * Busy-wait delay functions and their macro forms.
 * mdelay(n) typically expands to a loop of udelay() calls.
 */
class BusyDelayFunction extends Function {
  BusyDelayFunction() {
    this.getName() in [
        "mdelay", "udelay", "ndelay",
        "__mdelay", "__udelay", "__ndelay",
        "__const_udelay", "__delay"
      ]
  }
}

/**
 * Functions known/likely to be invoked in atomic context.
 * Heuristic: IRQ handlers, tasklets, timers, spinlock-held callers, etc.
 */
class AtomicContextFunction extends Function {
  AtomicContextFunction() {
    // Name-based heuristic for atomic-context callbacks.
    this.getName().regexpMatch("(?i).*(irq_handler|interrupt|tasklet|timer_fn|softirq|nmi).*")
    or
    // Functions that call spinlock acquisition without releasing before delay
    // — handled separately via call-chain in mayRunInAtomic.
    exists(FunctionCall fc |
      fc.getEnclosingFunction() = this and
      fc.getTarget().getName() in [
          "spin_lock", "spin_lock_irq", "spin_lock_irqsave",
          "spin_lock_bh", "raw_spin_lock", "raw_spin_lock_irq",
          "raw_spin_lock_irqsave", "raw_spin_lock_bh",
          "read_lock", "read_lock_irq", "read_lock_irqsave", "read_lock_bh",
          "write_lock", "write_lock_irq", "write_lock_irqsave", "write_lock_bh",
          "rcu_read_lock", "rcu_read_lock_bh", "rcu_read_lock_sched",
          "local_irq_disable", "local_irq_save",
          "preempt_disable"
        ]
    )
  }
}

/**
 * A function transitively callable only from non-atomic contexts.
 * Heuristic: function is a .probe / init / open / module_init / ioctl-like
 * entry, or only reachable from such entries. We approximate by checking
 * the function is named like a probe/init/setup and the call sites in the
 * file don't appear inside locked regions.
 */
predicate looksLikeProbeOrInit(Function f) {
  f.getName().regexpMatch("(?i).*(probe|_init|_setup|_open|_release|_remove|_attach|_detach|_bind|_unbind|module_init|module_exit).*")
}

/**
 * A call to a busy-wait delay primitive that is not inside any lock-held
 * or atomic region and whose enclosing function looks non-atomic.
 */
predicate calledInNonAtomicEnclosing(FunctionCall fc) {
  exists(Function caller |
    caller = fc.getEnclosingFunction() and
    not caller instanceof AtomicContextFunction and
    looksLikeProbeOrInit(caller)
  )
}

/**
 * The call is not preceded (in the same function, syntactically before)
 * by an unmatched atomic-context entry.
 */
predicate noPrecedingLock(FunctionCall delayCall) {
  not exists(FunctionCall lockCall |
    lockCall.getEnclosingFunction() = delayCall.getEnclosingFunction() and
    lockCall.getTarget().getName() in [
        "spin_lock", "spin_lock_irq", "spin_lock_irqsave",
        "spin_lock_bh", "raw_spin_lock", "raw_spin_lock_irq",
        "raw_spin_lock_irqsave", "raw_spin_lock_bh",
        "rcu_read_lock", "rcu_read_lock_bh",
        "local_irq_disable", "local_irq_save",
        "preempt_disable"
      ] and
    lockCall.getLocation().getStartLine() < delayCall.getLocation().getStartLine() and
    not exists(FunctionCall unlockCall |
      unlockCall.getEnclosingFunction() = delayCall.getEnclosingFunction() and
      unlockCall.getTarget().getName() in [
          "spin_unlock", "spin_unlock_irq", "spin_unlock_irqrestore",
          "spin_unlock_bh", "raw_spin_unlock", "raw_spin_unlock_irq",
          "raw_spin_unlock_irqrestore", "raw_spin_unlock_bh",
          "rcu_read_unlock", "rcu_read_unlock_bh",
          "local_irq_enable", "local_irq_restore",
          "preempt_enable"
        ] and
      unlockCall.getLocation().getStartLine() > lockCall.getLocation().getStartLine() and
      unlockCall.getLocation().getStartLine() < delayCall.getLocation().getStartLine()
    )
  )
}

/**
 * The delay duration (when a literal) is "long" (>= 1 ms equivalent),
 * which is where switching to msleep matters most.
 */
predicate isLongDelay(FunctionCall fc) {
  exists(int n |
    n = fc.getArgument(0).getValue().toInt() and
    (
      fc.getTarget().getName() in ["mdelay", "__mdelay"] and n >= 1
      or
      fc.getTarget().getName() in ["udelay", "__udelay", "__const_udelay"] and n >= 1000
      or
      fc.getTarget().getName() in ["ndelay", "__ndelay"] and n >= 1000000
    )
  )
}

from FunctionCall delayCall, Function caller
where
  delayCall.getTarget() instanceof BusyDelayFunction and
  caller = delayCall.getEnclosingFunction() and
  calledInNonAtomicEnclosing(delayCall) and
  noPrecedingLock(delayCall) and
  isLongDelay(delayCall)
select delayCall,
  "Busy-wait '" + delayCall.getTarget().getName() +
    "' called in apparently non-atomic function '" + caller.getName() +
    "'; consider replacing with msleep()/usleep_range()."
