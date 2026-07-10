/**
 * @name Busy-wait mdelay() used in a sleepable context
 * @description Detects calls to mdelay()/udelay() (busy-wait delays) in functions
 *              that are known to be safe to sleep. In such contexts the caller
 *              should use msleep()/usleep_range() instead so the CPU is not held
 *              spinning for long delays.
 * @kind problem
 * @problem.severity warning
 * @id cpp/busy-wait-in-sleepable-context
 * @tags correctness
 *       performance
 *       linux-kernel
 */

import cpp

/** A long busy-wait delay primitive that should be replaced with a sleeping variant. */
class BusyDelayCall extends FunctionCall {
  BusyDelayCall() {
    this.getTarget().getName() = "mdelay"
    or
    // udelay with a large constant is also suspicious in sleepable context.
    this.getTarget().getName() = "udelay" and
    exists(int v | v = this.getArgument(0).getValue().toInt() and v >= 1000)
  }

  int getDelayMs() {
    this.getTarget().getName() = "mdelay" and
    result = this.getArgument(0).getValue().toInt()
    or
    this.getTarget().getName() = "udelay" and
    result = this.getArgument(0).getValue().toInt() / 1000
  }
}

/** A function known to be invoked only in a sleepable context. */
predicate sleepableFunction(Function f) {
  // Power-management callbacks: suspend/resume/freeze/thaw/restore variants.
  f.getName().regexpMatch("(?i).*(_|^)(suspend|resume|freeze|thaw|restore|poweroff)(_.*|$)")
  or
  // Probe / remove / shutdown / init / release for buses are always called in
  // process context where sleeping is allowed.
  f.getName().regexpMatch("(?i).*(_|^)(probe|remove|shutdown|init|release|open|close|disconnect)(_.*|$)")
  or
  // Workqueue handler convention: void name(struct work_struct *).
  exists(Parameter p |
    p = f.getAParameter() and
    p.getType().getName().matches("%work_struct%")
  )
  or
  // Functions that themselves call a known sleeping primitive — by definition
  // they must run in sleepable context.
  exists(FunctionCall sleepCall |
    sleepCall.getEnclosingFunction() = f and
    sleepCall.getTarget().getName() in [
        "msleep", "msleep_interruptible", "usleep_range",
        "schedule", "schedule_timeout", "schedule_timeout_uninterruptible",
        "schedule_timeout_interruptible",
        "wait_for_completion", "wait_for_completion_interruptible",
        "wait_for_completion_timeout",
        "mutex_lock", "mutex_lock_interruptible",
        "down", "down_interruptible",
        "kmalloc", "kzalloc", "kcalloc"
      ] and
    // Exclude trivial GFP_ATOMIC allocations as evidence of sleepable context
    not sleepCall.getTarget().getName().matches("k%alloc")
  )
}

from BusyDelayCall call, Function f
where
  f = call.getEnclosingFunction() and
  sleepableFunction(f) and
  call.getDelayMs() >= 10
select call,
  "Busy-wait " + call.getTarget().getName() + "(" + call.getDelayMs().toString() +
    "ms) in sleepable function '" + f.getName() + "'; consider msleep()/usleep_range() instead."
