/**
 * @name Busy-wait mdelay in non-atomic context
 * @description Detects calls to mdelay() (and friends like ndelay/udelay used for
 *              long waits) from functions that execute in process / sleepable
 *              context (e.g. workqueue handlers, ioctl/read/write file ops,
 *              probe/remove callbacks). In sleepable context the CPU should
 *              not be busy-waited; usleep_range() / msleep() should be used
 *              instead. This is the pattern fixed by commits like
 *              "PCI: endpoint: Replace mdelay with usleep_range() in
 *              pci_epf_test_write()".
 * @kind problem
 * @problem.severity warning
 * @id cpp/busy-wait-in-sleepable-context
 * @tags performance
 *       correctness
 */

import cpp
import semmle.code.cpp.controlflow.Guards

/**
 * A call to a busy-waiting delay primitive that blocks the CPU for at least
 * ~1ms. We focus on mdelay (definitely >=1ms busy-wait); we also consider
 * udelay called with large constants, and ndelay similarly, since those are
 * the same anti-pattern.
 */
class BusyDelayCall extends FunctionCall {
  BusyDelayCall() {
    this.getTarget().getName() = "mdelay"
    or
    // udelay(>=1000) is effectively a >=1ms busy wait
    this.getTarget().getName() = "udelay" and
    exists(int n |
      n = this.getArgument(0).getValue().toInt() and n >= 1000
    )
    or
    // ndelay(>=1_000_000) similarly
    this.getTarget().getName() = "ndelay" and
    exists(int n |
      n = this.getArgument(0).getValue().toInt() and n >= 1000000
    )
  }
}

/**
 * Functions that appear (by name or by how they are registered) to run in
 * sleepable / process context, not in atomic context. This intentionally
 * stays conservative -- we want patterns analogous to pci_epf_test_write
 * (a function reachable from a delayed_work / workqueue handler, or a file
 * op like .write).
 */
predicate isSleepableContextFunction(Function f) {
  // Workqueue / delayed_work handler shape: takes a single struct work_struct *
  // (most kernel work fns are of this form). We approximate by parameter type
  // name.
  exists(Parameter p |
    p = f.getAParameter() and
    p.getType().getUnspecifiedType().(PointerType).getBaseType().getName() = "work_struct"
  )
  or
  // File operations write/read/ioctl-like callbacks (often *_write / *_read).
  f.getName().regexpMatch("(?i).*_(write|read|ioctl|open|release|store|show|probe|remove|suspend|resume|setup|prepare|configure|init_module|exit_module)$")
  or
  // Functions whose body itself sleeps via a known sleeping API are
  // demonstrably sleepable.
  exists(FunctionCall c |
    c.getEnclosingFunction() = f and
    c.getTarget().getName() in [
        "msleep", "msleep_interruptible", "usleep_range",
        "schedule", "schedule_timeout", "schedule_timeout_interruptible",
        "wait_event_interruptible", "wait_for_completion",
        "kmalloc", "kzalloc", "vmalloc"
      ] and
    // kmalloc with GFP_KERNEL specifically may sleep
    (
      not c.getTarget().getName().matches("k%alloc")
      or
      exists(Expr gfp | gfp = c.getArgument(c.getNumberOfArguments() - 1) |
        gfp.toString().matches("%GFP_KERNEL%"))
    )
  )
}

/**
 * A function transitively callable from a sleepable-context function and
 * which itself contains a busy-wait delay call. We bound the search to
 * keep the predicate cheap: depth-2 call chain.
 */
predicate reachableFromSleepable(Function f) {
  isSleepableContextFunction(f)
  or
  exists(Function caller, FunctionCall c |
    isSleepableContextFunction(caller) and
    c.getEnclosingFunction() = caller and
    c.getTarget() = f
  )
}

/**
 * A function is "atomic-marked" if it (or a transitive caller along the
 * chain we examined) takes a spinlock or disables preemption/irqs without
 * releasing before the delay -- we suppress those.
 */
predicate inAtomicSection(BusyDelayCall bd) {
  exists(FunctionCall lock |
    lock.getEnclosingFunction() = bd.getEnclosingFunction() and
    lock.getTarget().getName().regexpMatch(
      "spin_lock.*|raw_spin_lock.*|local_irq_disable|preempt_disable|rcu_read_lock.*"
    ) and
    lock.getLocation().getStartLine() < bd.getLocation().getStartLine() and
    not exists(FunctionCall unlock |
      unlock.getEnclosingFunction() = bd.getEnclosingFunction() and
      unlock.getTarget().getName().regexpMatch(
        "spin_unlock.*|raw_spin_unlock.*|local_irq_enable|preempt_enable|rcu_read_unlock.*"
      ) and
      unlock.getLocation().getStartLine() > lock.getLocation().getStartLine() and
      unlock.getLocation().getStartLine() < bd.getLocation().getStartLine()
    )
  )
}

from BusyDelayCall bd, Function f
where
  f = bd.getEnclosingFunction() and
  reachableFromSleepable(f) and
  not inAtomicSection(bd)
select bd,
  "Busy-wait '" + bd.getTarget().getName() +
    "' called from sleepable context function '" + f.getName() +
    "'; consider usleep_range()/msleep() instead."
