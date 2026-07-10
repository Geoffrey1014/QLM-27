/**
 * @name Busy-wait mdelay in sleepable context
 * @description Finds calls to mdelay() (and friends like ndelay/udelay with large
 *              constants) inside functions that are reachable only from
 *              sleepable contexts (e.g., PCI/platform .probe, ioctl, sysfs store,
 *              module_init). Such busy-waits unnecessarily burn CPU and should be
 *              replaced with msleep()/usleep_range().
 * @kind problem
 * @problem.severity warning
 * @id cpp/busy-wait-in-sleepable-context
 * @tags performance
 *       correctness
 */

import cpp
import semmle.code.cpp.controlflow.IRGuards

/**
 * A call to a busy-wait delay routine that, when called with a "large" amount,
 * is a candidate for replacement with a sleeping primitive.
 */
class BusyWaitCall extends FunctionCall {
  BusyWaitCall() {
    // mdelay() is always milliseconds of busy-wait — anything > ~10us is suspect.
    this.getTarget().hasName("mdelay")
    or
    // udelay() with a constant of at least 1000 (= 1ms) is also a candidate;
    // shorter waits are often legitimately atomic (e.g. PCIe link training).
    this.getTarget().hasName("udelay") and
    exists(int v | v = this.getArgument(0).getValue().toInt() | v >= 1000)
    or
    // __delay/__const_udelay variants
    this.getTarget().hasName("__delay")
  }
}

/**
 * Functions that are statically known to execute in an atomic / non-sleepable
 * context.  If a busy-wait sits inside one of these (transitively), the patch
 * pattern (replace with msleep) does NOT apply — keep it silent.
 */
class AtomicContextFunction extends Function {
  AtomicContextFunction() {
    // Interrupt / softirq / tasklet handlers — heuristic by name and by
    // being assigned to a struct field commonly used for IRQ handlers.
    exists(string n | n = this.getName() |
      n.matches("%_irq_handler") or
      n.matches("%_interrupt") or
      n.matches("%_isr") or
      n.matches("%_tasklet%")
    )
    or
    // Functions that themselves acquire a spinlock and have not released it
    // before the busy-wait would be silly to flag — but we conservatively
    // treat any function containing a spin_lock* call as potentially atomic.
    exists(FunctionCall fc |
      fc.getEnclosingFunction() = this and
      (
        fc.getTarget().getName().matches("spin_lock%") or
        fc.getTarget().getName().matches("raw_spin_lock%") or
        fc.getTarget().getName().matches("rcu_read_lock%") or
        fc.getTarget().getName() = "local_irq_disable" or
        fc.getTarget().getName() = "preempt_disable"
      )
    )
  }
}

/**
 * Holds if `caller` may invoke `callee` directly via a normal function call.
 */
predicate calls(Function caller, Function callee) {
  exists(FunctionCall fc |
    fc.getEnclosingFunction() = caller and
    fc.getTarget() = callee
  )
}

/**
 * Transitive caller closure (bounded by definition of `calls`).
 */
predicate callsTransitively(Function caller, Function callee) {
  calls(caller, callee)
  or
  exists(Function mid | calls(caller, mid) and callsTransitively(mid, callee))
}

/**
 * A function is reachable from an atomic context if it itself is atomic, or
 * if any of its (transitive) callers is atomic.
 */
predicate reachableFromAtomic(Function f) {
  f instanceof AtomicContextFunction
  or
  exists(AtomicContextFunction af | callsTransitively(af, f))
}

/**
 * Heuristic indicators that a function is invoked in a clearly sleepable
 * context — assigned to ".probe" of a pci_driver / platform_driver, or
 * named like an ioctl/sysfs/store/show/init handler, or used as a workqueue
 * worker.  Used as a positive signal to raise confidence.
 */
predicate sleepableContextFunction(Function f) {
  exists(string n | n = f.getName() |
    n.matches("%_probe") or
    n.matches("%_init") or
    n.matches("%_remove") or
    n.matches("%_open") or
    n.matches("%_release") or
    n.matches("%_ioctl") or
    n.matches("%_store") or
    n.matches("%_show") or
    n.matches("%_work") or
    n.matches("%_worker") or
    n.matches("%_thread")
  )
}

/**
 * A function is "sleepable" if some transitive caller looks like a sleepable
 * entry point AND no transitive caller looks atomic.
 */
predicate inSleepableContextOnly(Function f) {
  (sleepableContextFunction(f) or
   exists(Function s | sleepableContextFunction(s) and callsTransitively(s, f))
  ) and
  not reachableFromAtomic(f)
}

from BusyWaitCall call, Function enclosing
where
  enclosing = call.getEnclosingFunction() and
  inSleepableContextOnly(enclosing) and
  // Avoid early-boot/arch code where msleep is unsafe.
  not enclosing.getFile().getRelativePath().matches("arch/%") and
  not enclosing.getFile().getRelativePath().matches("init/%")
select call,
  "Busy-wait '" + call.getTarget().getName() +
    "' in '" + enclosing.getName() +
    "' which appears reachable only from sleepable context; consider msleep()/usleep_range()."
