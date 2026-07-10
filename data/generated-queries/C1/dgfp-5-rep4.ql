/**
 * @name Busy-wait via mdelay() inside a sleepable context
 * @description A call to mdelay() (CPU-busy delay) appears in a function that
 *              is reachable only from non-atomic / sleepable contexts (e.g. a
 *              suspend/resume callback, a probe/open handler, a workqueue
 *              handler, or any function that already calls a sleeping
 *              primitive such as msleep / usleep_range / schedule_timeout).
 *              In such contexts the correct primitive is usleep_range() or
 *              msleep(), which yield the CPU. This is the "delay-gfp" / DCNS
 *              pattern: mdelay used where a sleeping delay is safe.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-dgfp-5
 */

import cpp

/** A call to one of the kernel's CPU-busy delay primitives. */
predicate isBusyDelayCall(FunctionCall fc) {
  exists(string n | n = fc.getTarget().getName() |
    n = "mdelay" or n = "udelay" or n = "ndelay"
  )
  and
  // Filter out short busy-waits: only mdelay-style millisecond-scale calls
  // are candidates for conversion to a sleeping delay. udelay()/ndelay() are
  // kept only when the literal argument is large enough that a sleep is sane.
  exists(Expr arg | arg = fc.getArgument(0) |
    fc.getTarget().getName() = "mdelay"
    or
    (fc.getTarget().getName() = "udelay" and arg.getValue().toInt() >= 1000)
  )
}

/** A call to a function that may sleep (yields CPU). Heuristic by name. */
predicate isSleepingCall(FunctionCall fc) {
  exists(string n | n = fc.getTarget().getName() |
    n = "msleep" or
    n = "msleep_interruptible" or
    n = "ssleep" or
    n = "schedule" or
    n = "schedule_timeout" or
    n = "schedule_timeout_uninterruptible" or
    n = "schedule_timeout_interruptible" or
    n = "wait_event" or
    n = "wait_event_interruptible" or
    n = "wait_event_timeout" or
    n.matches("usleep_range%") or
    n = "mutex_lock" or
    n = "mutex_lock_interruptible" or
    n = "down" or
    n = "down_interruptible" or
    // kmalloc/kzalloc/etc. with GFP_KERNEL may sleep — a strong indicator
    // that the enclosing function runs in process / sleepable context.
    n = "kmalloc" or
    n = "kzalloc" or
    n = "kcalloc" or
    n = "kmalloc_array" or
    n = "krealloc" or
    n = "vmalloc" or
    n = "vzalloc" or
    n = "kmem_cache_alloc"
  )
}

/**
 * A function whose name marks it as a non-atomic / sleepable callback: PM
 * suspend/resume hooks, driver probe/open/release hooks, init/exit code,
 * sysfs show/store, workqueue handlers, threads, etc. These are
 * conventionally allowed to sleep.
 */
predicate isSleepableContextFunction(Function f) {
  exists(string n | n = f.getName() |
    n.matches("%resume%") or
    n.matches("%suspend%") or
    n.matches("%probe%") or
    n.matches("%_remove") or
    n.matches("%_remove_%") or
    n.matches("%_open") or
    n.matches("%_open_%") or
    n.matches("%_release") or
    n.matches("%_init") or
    n.matches("%_init_%") or
    n.matches("%_exit") or
    n.matches("%_show") or
    n.matches("%_store") or
    n.matches("%_thread") or
    n.matches("%_work") or
    n.matches("%_workfn") or
    n.matches("%_handler") or
    n.matches("%_write") or
    n.matches("%_read") or
    n.matches("%_ioctl")
  )
}

/**
 * A function we consider sleepable because it either (a) is named like a
 * sleepable callback, or (b) itself already invokes a sleeping primitive
 * somewhere in its body.
 */
predicate inSleepableContext(Function f) {
  isSleepableContextFunction(f)
  or
  exists(FunctionCall fc |
    fc.getEnclosingFunction() = f and
    isSleepingCall(fc)
  )
}

from FunctionCall delayCall, Function f
where
  isBusyDelayCall(delayCall) and
  f = delayCall.getEnclosingFunction() and
  inSleepableContext(f) and
  // exclude irq / atomic / spinlock-named contexts (defence in depth)
  not exists(string n | n = f.getName() |
    n.matches("%_irq") or
    n.matches("%_isr") or
    n.matches("%_atomic%") or
    n.matches("%_spin%")
  )
select delayCall,
  "Busy-wait via " + delayCall.getTarget().getName() +
    "() inside sleepable context function $@; consider usleep_range() instead.",
  f, f.getName()
