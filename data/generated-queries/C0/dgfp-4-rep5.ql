/**
 * @name Unnecessary GFP_ATOMIC in sleepable context
 * @description Detects calls passing GFP_ATOMIC inside a function that is
 *              demonstrably sleepable (it calls a known sleeping function or
 *              also uses GFP_KERNEL itself). In such functions GFP_ATOMIC is
 *              unnecessary and should be GFP_KERNEL, matching the
 *              em28xx_init_usb_xfer() class of fixes.
 * @kind problem
 * @problem.severity warning
 * @id cpp/delay-gfp-atomic-in-sleepable
 * @tags correctness
 *       performance
 *       reliability
 */

import cpp

/**
 * A macro invocation of GFP_ATOMIC appearing as (or inside) an argument of a call.
 * GFP_ATOMIC is a macro (#define GFP_ATOMIC (__GFP_HIGH|__GFP_KSWAPD_RECLAIM)).
 */
predicate isGfpAtomicArg(Call call, int argIdx) {
  exists(MacroInvocation mi |
    mi.getMacroName() = "GFP_ATOMIC" and
    mi.getEnclosingElement*() = call.getArgument(argIdx)
  )
}

/**
 * A macro invocation of GFP_KERNEL appearing as (or inside) an argument of a call.
 */
predicate isGfpKernelArg(Call call, int argIdx) {
  exists(MacroInvocation mi |
    mi.getMacroName() = "GFP_KERNEL" and
    mi.getEnclosingElement*() = call.getArgument(argIdx)
  )
}

/**
 * Functions that may sleep: a curated subset of well-known sleeping APIs in
 * the Linux kernel. If a function f calls any of these, then f is sleepable
 * (at least on some path), and any GFP_ATOMIC in f along a non-atomic path
 * is suspicious.
 */
predicate isSleepingFunctionName(string n) {
  n = "msleep" or
  n = "msleep_interruptible" or
  n = "usleep_range" or
  n = "ssleep" or
  n = "schedule" or
  n = "schedule_timeout" or
  n = "schedule_timeout_interruptible" or
  n = "schedule_timeout_uninterruptible" or
  n = "mutex_lock" or
  n = "mutex_lock_interruptible" or
  n = "mutex_lock_killable" or
  n = "down" or
  n = "down_interruptible" or
  n = "down_killable" or
  n = "down_read" or
  n = "down_write" or
  n = "wait_event" or
  n = "wait_event_interruptible" or
  n = "wait_event_timeout" or
  n = "wait_for_completion" or
  n = "wait_for_completion_interruptible" or
  n = "wait_for_completion_timeout"
}

/**
 * Holds if f is sleepable: it calls some known sleeping function, OR it
 * itself passes GFP_KERNEL to some allocator (which implies the caller
 * already believed the context is sleepable).
 */
predicate isSleepableFunction(Function f) {
  exists(FunctionCall fc |
    fc.getEnclosingFunction() = f and
    isSleepingFunctionName(fc.getTarget().getName())
  )
  or
  exists(Call c, int i |
    c.getEnclosingFunction() = f and
    isGfpKernelArg(c, i)
  )
}

/**
 * Holds if f looks like an atomic-context entry point that legitimately
 * needs GFP_ATOMIC: an IRQ handler, tasklet, timer callback, or similar.
 * Heuristic: name ends in "_irq", "_isr", "_tasklet", "_timer", or starts
 * with "tasklet_". Used to suppress obvious true-need cases.
 */
predicate looksAtomicEntryPoint(Function f) {
  f.getName().matches("%_irq") or
  f.getName().matches("%_isr") or
  f.getName().matches("%_handler") or
  f.getName().matches("%_tasklet") or
  f.getName().matches("%_timer") or
  f.getName().matches("tasklet_%") or
  f.getName().matches("%_interrupt")
}

/**
 * Holds if the call sits in a basic block that is dominated by some
 * spin_lock-family call within the same function (i.e. a spin-lock is
 * held). Approximate: any spin_lock* call appears textually earlier in
 * the same function. We use this only to filter out obvious atomic
 * regions; we do not try to be sound.
 */
predicate underSpinLock(Call call) {
  exists(FunctionCall lockCall |
    lockCall.getEnclosingFunction() = call.getEnclosingFunction() and
    lockCall.getTarget().getName().matches("spin_lock%") and
    lockCall.getLocation().getStartLine() < call.getLocation().getStartLine() and
    not exists(FunctionCall unlockCall |
      unlockCall.getEnclosingFunction() = call.getEnclosingFunction() and
      unlockCall.getTarget().getName().matches("spin_unlock%") and
      unlockCall.getLocation().getStartLine() > lockCall.getLocation().getStartLine() and
      unlockCall.getLocation().getStartLine() < call.getLocation().getStartLine()
    )
  )
}

from Call call, Function enclosing, int argIdx
where
  isGfpAtomicArg(call, argIdx) and
  enclosing = call.getEnclosingFunction() and
  isSleepableFunction(enclosing) and
  not looksAtomicEntryPoint(enclosing) and
  not underSpinLock(call)
select call,
  "Call passes GFP_ATOMIC to '" + call.getTarget().getName() +
    "' inside sleepable function '" + enclosing.getName() +
    "'. GFP_ATOMIC may be unnecessary; consider GFP_KERNEL."
