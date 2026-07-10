/**
 * @name Busy-wait mdelay() in non-atomic sleepable context
 * @description Detects calls to mdelay()/udelay() (busy-wait CPU spinners) inside
 *              functions that are safely sleepable (PM resume/suspend, probe,
 *              ioctl, file operations, work-queue handlers, etc.) where msleep()
 *              or usleep_range() should be used to avoid wasting CPU cycles.
 *              Mirrors the wdt87xx_i2c wdt87xx_resume() fix (commit e58650b57ee0)
 *              and the broader DCNS/DSAC family of unnecessary-busy-wait bugs.
 * @kind problem
 * @problem.severity warning
 * @id cpp/unnecessary-mdelay-in-sleepable-context
 * @tags efficiency
 *       performance
 *       correctness
 */

import cpp
import semmle.code.cpp.controlflow.Guards

/**
 * Busy-wait delay APIs that block the CPU without yielding. These are only
 * required in true atomic contexts; in a sleepable function they waste CPU
 * (and on long delays, hurt latency).
 */
class BusyDelayCall extends FunctionCall {
  BusyDelayCall() {
    exists(string n | n = this.getTarget().getName() |
      n = "mdelay" or
      n = "__mdelay" or
      n = "udelay" or
      n = "__udelay" or
      n = "ndelay"
    )
  }

  /** Returns the delay argument as a constant millisecond/microsecond value, if known. */
  int getConstantArg() { result = this.getArgument(0).getValue().toInt() }
}

/**
 * A function whose name strongly implies it runs in process / sleepable
 * context. We use a name-based heuristic (the patched function is
 * `wdt87xx_resume`, and the DSAC/DCNS literature shows this pattern repeats
 * across PM, probe, open/release, ioctl, work handlers, and explicit *_sleep
 * helpers).
 */
class SleepableContextFunction extends Function {
  SleepableContextFunction() {
    exists(string n | n = this.getName().toLowerCase() |
      n.matches("%_resume") or
      n.matches("%_suspend") or
      n.matches("%_probe") or
      n.matches("%_open") or
      n.matches("%_release") or
      n.matches("%_ioctl") or
      n.matches("%_unlocked_ioctl") or
      n.matches("%_compat_ioctl") or
      n.matches("%_read") or
      n.matches("%_write") or
      n.matches("%_init") or
      n.matches("%_exit") or
      n.matches("%_remove") or
      n.matches("%_shutdown") or
      n.matches("%_thread") or
      n.matches("%_work") or
      n.matches("%_worker") or
      n.matches("%_workfn") or
      n.matches("%_handler_thread")
    )
  }
}

/**
 * Approximation of "currently inside an atomic region": the function (or the
 * call site) is guarded by spin_lock / local_irq_disable / preempt_disable /
 * rcu_read_lock. We only need to *exclude* obvious atomic call sites, so
 * approximate it conservatively as: the enclosing function calls any of these
 * acquire primitives anywhere before/around the delay.
 */
predicate inAtomicRegion(BusyDelayCall c) {
  exists(FunctionCall acq |
    acq.getEnclosingFunction() = c.getEnclosingFunction() and
    acq.getLocation().getStartLine() < c.getLocation().getStartLine() and
    exists(string an | an = acq.getTarget().getName() |
      an.matches("spin_lock%") or
      an.matches("raw_spin_lock%") or
      an.matches("read_lock%") or
      an.matches("write_lock%") or
      an = "local_irq_disable" or
      an = "local_irq_save" or
      an = "preempt_disable" or
      an = "rcu_read_lock" or
      an = "rcu_read_lock_bh" or
      an = "rcu_read_lock_sched"
    ) and
    // No matching release between acq and c
    not exists(FunctionCall rel |
      rel.getEnclosingFunction() = c.getEnclosingFunction() and
      rel.getLocation().getStartLine() > acq.getLocation().getStartLine() and
      rel.getLocation().getStartLine() < c.getLocation().getStartLine() and
      exists(string rn | rn = rel.getTarget().getName() |
        rn.matches("spin_unlock%") or
        rn.matches("raw_spin_unlock%") or
        rn.matches("read_unlock%") or
        rn.matches("write_unlock%") or
        rn = "local_irq_enable" or
        rn = "local_irq_restore" or
        rn = "preempt_enable" or
        rn = "rcu_read_unlock" or
        rn = "rcu_read_unlock_bh" or
        rn = "rcu_read_unlock_sched"
      )
    )
  )
}

/**
 * Is the enclosing function annotated/named as an interrupt or atomic-only
 * routine? Used as a second exclusion filter.
 */
predicate likelyAtomicFunction(Function f) {
  exists(string n | n = f.getName().toLowerCase() |
    n.matches("%_isr") or
    n.matches("%_irq") or
    n.matches("%_irq_handler") or
    n.matches("%_interrupt") or
    n.matches("%_tasklet") or
    n.matches("%_timer") or
    n.matches("%_timer_fn") or
    n.matches("%_hrtimer") or
    n.matches("%_nmi")
  )
}

from BusyDelayCall c, SleepableContextFunction f, int ms
where
  c.getEnclosingFunction() = f and
  not likelyAtomicFunction(f) and
  not inAtomicRegion(c) and
  // Only flag delays >= 1 ms total (mdelay >=1, udelay >=1000) — these are the
  // ones DCNS/DSAC actually targets; sub-millisecond busy-waits are usually
  // intentional even in sleepable code.
  (
    (c.getTarget().getName() = "mdelay" and ms = c.getConstantArg() and ms >= 1) or
    (c.getTarget().getName() = "__mdelay" and ms = c.getConstantArg() and ms >= 1) or
    (c.getTarget().getName() = "udelay" and ms = c.getConstantArg() / 1000 and c.getConstantArg() >= 1000)
  )
select c,
  "Busy-wait " + c.getTarget().getName() + "(" + ms.toString() +
    " ms equivalent) in sleepable function $@ — consider msleep()/usleep_range() instead.",
  f, f.getName()
