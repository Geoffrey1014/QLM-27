/**
 * @name Busy-wait (mdelay/udelay/ndelay) used in sleep-capable context
 * @description The enclosing function performs a sleepable operation
 *              (kmalloc/kzalloc/kcalloc/vmalloc family — all of which
 *              can sleep with GFP_KERNEL semantics), so the kernel is
 *              free to schedule the function out. Burning CPU with a
 *              busy-wait primitive (mdelay / udelay / ndelay) in that
 *              context wastes cycles; usleep_range() / msleep() would
 *              cooperatively yield. This is the "delay-gfp" pattern
 *              targeted by Jia-Ju Bai's DSAC-family fixes (e.g. Linux
 *              commit 9f96b9b7d836).
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-dgfp-5
 */

import cpp

/* Busy-wait primitives that hog the CPU and never yield. */
predicate isBusyWaitApi(string name) {
  name = "mdelay" or
  name = "udelay" or
  name = "ndelay"
}

/* Allocator primitives that ride the page-allocator slow path and are
 * therefore allowed to sleep. Their presence in a function is strong
 * evidence the function is in a sleep-capable context. */
predicate isSleepCapableApi(string name) {
  name = "kmalloc" or
  name = "kzalloc" or
  name = "kcalloc" or
  name = "krealloc" or
  name = "kmemdup" or
  name = "kstrdup" or
  name = "vmalloc" or
  name = "vzalloc" or
  name = "kvmalloc" or
  name = "kvzalloc" or
  name = "devm_kmalloc" or
  name = "devm_kzalloc" or
  name = "devm_kcalloc" or
  name = "mutex_lock" or
  name = "down" or
  name = "down_interruptible" or
  name = "wait_event" or
  name = "msleep" or
  name = "usleep_range" or
  name = "schedule" or
  name = "schedule_timeout"
}

/* True when function f also calls a sleep-capable primitive. */
predicate functionIsSleepCapable(Function f) {
  exists(FunctionCall c |
    c.getEnclosingFunction() = f and
    isSleepCapableApi(c.getTarget().getName())
  )
}

from FunctionCall busy, Function f, string busyName
where
  busyName = busy.getTarget().getName() and
  isBusyWaitApi(busyName) and
  f = busy.getEnclosingFunction() and
  functionIsSleepCapable(f)
select busy,
  "Busy-wait '" + busyName +
    "' called inside '" + f.getName() +
    "', which also performs sleep-capable operations -- prefer usleep_range()/msleep()."
