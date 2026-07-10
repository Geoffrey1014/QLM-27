/**
 * @name Unnecessary mdelay() in sleepable context
 * @description Calls to mdelay() perform a busy-wait that monopolizes the CPU.
 *              When the surrounding function is known to run in a sleepable
 *              (process / non-atomic) context — e.g. PM resume/suspend hooks,
 *              probe/remove callbacks, ioctl/read/write fops, work_struct
 *              handlers, or kernel threads — mdelay() should be replaced
 *              by msleep() (or usleep_range() for short waits) so the CPU
 *              can be yielded to other tasks.
 * @kind problem
 * @problem.severity warning
 * @id cpp/kernel-mdelay-in-sleepable-context
 * @tags performance
 *       correctness
 */

import cpp

/**
 * A call to mdelay() (or its wrappers) — the busy-wait family we want to flag
 * when used outside an atomic context.
 */
class MdelayCall extends FunctionCall {
  MdelayCall() {
    this.getTarget().getName() = "mdelay"
  }
}

/**
 * A function whose name / signature strongly indicates it runs in a sleepable
 * (process) context, never under a spinlock, IRQ handler or RCU read side.
 *
 * The patterns below are deliberately conservative: each matches a function
 * role for which the kernel contract guarantees process context (so calling
 * msleep() / mutex_lock() inside is safe and idiomatic, and mdelay() is
 * therefore unnecessary busy-waiting).
 */
predicate isSleepableContextFunction(Function f) {
  exists(string n | n = f.getName() |
    // Power-management device callbacks — invoked from PM core in process ctx
    n.matches("%_resume") or
    n.matches("%_suspend") or
    n.matches("%_freeze") or
    n.matches("%_thaw") or
    n.matches("%_poweroff") or
    n.matches("%_restore") or
    n.matches("%_runtime_resume") or
    n.matches("%_runtime_suspend") or
    // Driver model lifecycle callbacks
    n.matches("%_probe") or
    n.matches("%_remove") or
    n.matches("%_shutdown") or
    // File-operations entry points (always called from syscall/process ctx)
    n.matches("%_open") or
    n.matches("%_release") or
    n.matches("%_ioctl") or
    n.matches("%_unlocked_ioctl") or
    n.matches("%_compat_ioctl") or
    n.matches("%_fops_read") or
    n.matches("%_fops_write") or
    // Workqueue handlers (work_struct.func) run in kworker process ctx
    n.matches("%_work") or
    n.matches("%_work_handler") or
    n.matches("%_work_fn") or
    // Kthread main functions
    n.matches("%_thread") or
    n.matches("%_kthread")
  )
}

/**
 * A function that is reachable from a (statically inferred) atomic context —
 * i.e. it might be called from a hard/soft IRQ handler, a timer callback,
 * a tasklet, or another well-known atomic entry point. We approximate this
 * by name patterns of known atomic roles and propagate one call-depth out
 * to skip helpers that are reused from both contexts.
 *
 * Used to suppress flags on mdelay() sites that may legitimately be reached
 * from atomic code paths even if the immediate caller looks sleepable.
 */
predicate mayRunInAtomicContext(Function f) {
  exists(string n | n = f.getName() |
    n.matches("%_isr") or
    n.matches("%_irq") or
    n.matches("%_irq_handler") or
    n.matches("%_interrupt") or
    n.matches("%_tasklet") or
    n.matches("%_timer") or
    n.matches("%_timer_fn") or
    n.matches("%_softirq")
  )
  or
  // Propagate one level: if f is called from a known atomic-context function,
  // it may itself run in atomic context.
  exists(Function caller, FunctionCall c |
    c.getEnclosingFunction() = caller and
    c.getTarget() = f and
    exists(string m | m = caller.getName() |
      m.matches("%_isr") or
      m.matches("%_irq") or
      m.matches("%_interrupt") or
      m.matches("%_tasklet") or
      m.matches("%_timer")
    )
  )
}

/**
 * The mdelay() argument is "large enough" that a busy-wait is wasteful:
 * msleep() is the documented replacement when the delay is >= a few ms.
 * For 0 / 1-ms delays the kernel style guide actually permits mdelay(),
 * so we conservatively only flag delays >= 10 ms (the threshold the kernel
 * Documentation/timers/timers-howto.rst recommends switching at).
 */
predicate isWastefulDelay(MdelayCall mc) {
  exists(int v | v = mc.getArgument(0).getValue().toInt() and v >= 10)
  or
  // If we can't statically evaluate the argument, still flag when it is
  // not a tiny integer literal — i.e. the conservative default is to warn.
  not exists(mc.getArgument(0).getValue().toInt())
}

from MdelayCall mc, Function enclosing
where
  enclosing = mc.getEnclosingFunction() and
  isSleepableContextFunction(enclosing) and
  not mayRunInAtomicContext(enclosing) and
  isWastefulDelay(mc)
select mc,
  "mdelay() busy-waits while $@ runs in a sleepable context; use msleep() (or usleep_range()) instead.",
  enclosing, enclosing.getName()
