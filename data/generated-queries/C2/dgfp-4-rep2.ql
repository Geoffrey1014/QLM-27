/**
 * @name  rq3-c2-dgfp-4-rep2
 * @id    cpp/rq3/c2/dgfp-4-rep2
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects GFP_ATOMIC allocations made from functions that
 *              also contain calls indicating a sleepable context.
 */

import cpp

/**
 * Holds if `e` is the GFP_ATOMIC allocation-flag macro expansion.
 * After macro expansion GFP_ATOMIC is an integer literal whose textual
 * source (via getValueText / the originating macro invocation) contains
 * the token "GFP_ATOMIC".
 */
predicate is_atomic_gfp_flag(Expr e) {
  exists(MacroInvocation mi |
    mi.getMacroName() = "GFP_ATOMIC" and
    mi.getExpr() = e
  )
  or
  // Fallback: the expression's source text mentions GFP_ATOMIC.
  exists(string s | s = e.toString() | s.matches("%GFP_ATOMIC%"))
}

/**
 * Names of kernel APIs that may sleep (a conservative subset).
 */
predicate sleeping_function_name(string name) {
  name = "msleep" or
  name = "msleep_interruptible" or
  name = "usleep_range" or
  name = "ssleep" or
  name = "schedule" or
  name = "schedule_timeout" or
  name = "schedule_timeout_interruptible" or
  name = "schedule_timeout_uninterruptible" or
  name = "mutex_lock" or
  name = "mutex_lock_interruptible" or
  name = "down" or
  name = "down_interruptible" or
  name = "down_killable" or
  name = "wait_event" or
  name = "wait_event_interruptible" or
  name = "wait_event_timeout" or
  name = "init_waitqueue_head" or
  name = "usb_clear_halt" or
  name = "usb_control_msg" or
  name = "usb_bulk_msg" or
  name = "kmalloc" or // not sleeping per se, but commonly used GFP_KERNEL path indicator
  name = "might_sleep"
}

/**
 * Holds if `fc` is a call to a function whose name appears in the
 * sleeping-API list.
 */
predicate is_sleeping_call(FunctionCall fc) {
  sleeping_function_name(fc.getTarget().getName())
}

/**
 * Holds if `f` (intraprocedurally) contains at least one call to a
 * sleeping API — a proxy for "f is callable from sleepable context".
 */
predicate function_may_sleep(Function f) {
  exists(FunctionCall fc |
    fc.getEnclosingFunction() = f and
    is_sleeping_call(fc)
  )
}

/**
 * Holds if `fc` passes GFP_ATOMIC as one of its arguments while being
 * inside a function that elsewhere performs a sleeping call.
 */
predicate vulnerable_gfp_atomic_call(FunctionCall fc) {
  exists(Expr arg |
    arg = fc.getAnArgument() and
    is_atomic_gfp_flag(arg)
  ) and
  function_may_sleep(fc.getEnclosingFunction())
}

from FunctionCall fc, Function enclosing
where
  vulnerable_gfp_atomic_call(fc) and
  enclosing = fc.getEnclosingFunction()
select fc,
  "GFP_ATOMIC used in call to '" + fc.getTarget().getName() +
  "' inside function '" + enclosing.getName() +
  "' which may run in sleepable context (consider GFP_KERNEL)."
