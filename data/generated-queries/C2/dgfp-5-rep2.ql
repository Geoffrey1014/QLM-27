/**
 * @name  rq3-c2-dgfp-5-rep2
 * @id    cpp/rq3/c2/dgfp-5-rep2
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Flags busy-wait calls (mdelay/udelay/ndelay) inside functions
 *              that appear to run in sleepable context, and so should use
 *              usleep_range / msleep instead.
 */

import cpp

predicate isBusyWaitCall(FunctionCall c) {
  exists(string n | n = c.getTarget().getName() |
    n = "mdelay" or n = "udelay" or n = "ndelay"
  )
}

predicate isSleepableGfpFlag(Expr e) {
  exists(string s | s = e.toString() |
    s = "GFP_KERNEL" or s = "GFP_USER" or s = "GFP_NOFS" or s = "GFP_NOIO" or
    s = "GFP_KERNEL_ACCOUNT" or s = "GFP_HIGHUSER" or s = "GFP_HIGHUSER_MOVABLE"
  )
}

predicate hasSleepableEvidence(Function f) {
  // Allocation with a sleepable GFP flag
  exists(FunctionCall a |
    a.getEnclosingFunction() = f and
    a.getTarget().getName() in [
      "kmalloc", "kzalloc", "kcalloc", "krealloc", "kmalloc_array",
      "kmemdup", "kstrdup", "kstrndup", "vmalloc", "vzalloc",
      "kmalloc_node", "kzalloc_node", "devm_kmalloc", "devm_kzalloc"
    ] and
    isSleepableGfpFlag(a.getAnArgument())
  )
  or
  // Direct sleepable call inside f
  exists(FunctionCall s |
    s.getEnclosingFunction() = f and
    s.getTarget().getName() in [
      "msleep", "msleep_interruptible", "usleep_range", "schedule",
      "schedule_timeout", "schedule_timeout_interruptible",
      "schedule_timeout_uninterruptible", "wait_event", "wait_event_interruptible",
      "wait_event_timeout", "wait_event_interruptible_timeout",
      "mutex_lock", "mutex_lock_interruptible", "down", "down_interruptible",
      "might_sleep", "ssleep"
    ]
  )
}

predicate inSleepableContext(FunctionCall c) {
  hasSleepableEvidence(c.getEnclosingFunction())
}

predicate isReplaceableBusyWait(FunctionCall c) {
  isBusyWaitCall(c) and inSleepableContext(c)
}

from FunctionCall c
where isReplaceableBusyWait(c)
select c,
  "Busy-wait (" + c.getTarget().getName() +
  ") in a function that performs sleepable operations; consider usleep_range/msleep."
