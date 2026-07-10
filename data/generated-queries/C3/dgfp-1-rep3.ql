/**
 * @name C3 generated query for dgfp-1 / fix e58650b57ee0
 * @description Busy-wait mdelay() (or large udelay) used in a function that
 *              is always invoked in sleepable context (PM callback,
 *              probe/remove/init, work_struct handler, or a function that
 *              already calls a sleeping primitive). Such a function should
 *              use msleep()/usleep_range() instead of busy-waiting.
 * @kind problem
 * @problem.severity warning
 * @id cpp/rq3/c3/dgfp-1-rep3
 */

import cpp

predicate isBusyDelayCall(FunctionCall fc) {
  fc.getTarget().getName() = "mdelay"
  or
  fc.getTarget().getName() = "udelay" and
  exists(int v | v = fc.getArgument(0).getValue().toInt() and v >= 1000)
}

int getDelayMs(FunctionCall fc) {
  isBusyDelayCall(fc) and
  (
    fc.getTarget().getName() = "mdelay" and
    result = fc.getArgument(0).getValue().toInt()
    or
    fc.getTarget().getName() = "udelay" and
    result = fc.getArgument(0).getValue().toInt() / 1000
  )
}

predicate isPmCallback(Function f) {
  f.getName().regexpMatch("(?i).*(_|^)(suspend|resume|freeze|thaw|restore|poweroff)(_.*|$)")
}

predicate isProcessContextFunction(Function f) {
  f.getName().regexpMatch("(?i).*(_|^)(probe|remove|shutdown|init|release|open|close|disconnect)(_.*|$)")
  or
  exists(Parameter p |
    p = f.getAParameter() and
    p.getType().getName().matches("%work_struct%")
  )
}

predicate callsSleepingPrimitive(Function f) {
  exists(FunctionCall sleepCall |
    sleepCall.getEnclosingFunction() = f and
    sleepCall.getTarget().getName() in [
        "msleep", "msleep_interruptible", "usleep_range",
        "schedule", "schedule_timeout",
        "schedule_timeout_uninterruptible",
        "schedule_timeout_interruptible",
        "wait_for_completion", "wait_for_completion_interruptible",
        "wait_for_completion_timeout",
        "mutex_lock", "mutex_lock_interruptible",
        "down", "down_interruptible"
      ]
  )
}

predicate isSleepableFunction(Function f) {
  isPmCallback(f) or isProcessContextFunction(f) or callsSleepingPrimitive(f)
}

from FunctionCall call, Function f, int ms
where
  isBusyDelayCall(call) and
  f = call.getEnclosingFunction() and
  isSleepableFunction(f) and
  ms = getDelayMs(call) and
  ms >= 10
select call,
  "Busy-wait " + call.getTarget().getName() + "(" + ms.toString() +
    "ms) in sleepable function '" + f.getName() + "'; consider msleep()/usleep_range() instead."
