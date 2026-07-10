/**
 * @name  rq3-c2-dgfp-4-rep4
 * @id    cpp/rq3/c2/dgfp-4-rep4
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects callsites passing GFP_ATOMIC to allocator-like APIs where
 *              the enclosing caller appears to be sleepable (non-atomic) context.
 */

import cpp

/* Predicate 1: identify an expression that is (or expands to) GFP_ATOMIC. */
predicate is_gfp_atomic_arg(Expr arg) {
  exists(MacroInvocation mi |
    mi.getMacroName() = "GFP_ATOMIC" and
    mi.getExpr() = arg
  )
  or
  arg.toString() = "GFP_ATOMIC"
  or
  exists(MacroInvocation mi |
    mi.getMacroName() = "GFP_ATOMIC" and
    mi.getAnExpandedElement() = arg
  )
}

/* Predicate 2: a FunctionCall passes GFP_ATOMIC as the idx-th argument. */
predicate call_with_gfp_atomic(FunctionCall fc, Function callee, int idx) {
  callee = fc.getTarget() and
  is_gfp_atomic_arg(fc.getArgument(idx))
}

/* Predicate 3: a function whose presence in the caller's body shows the caller
 * itself is sleepable (because these functions may sleep / require process ctx). */
predicate func_may_sleep_in_caller(Function f) {
  f.getName() = "msleep" or
  f.getName() = "msleep_interruptible" or
  f.getName() = "ssleep" or
  f.getName() = "usleep_range" or
  f.getName() = "schedule" or
  f.getName() = "schedule_timeout" or
  f.getName() = "schedule_timeout_interruptible" or
  f.getName() = "mutex_lock" or
  f.getName() = "mutex_lock_interruptible" or
  f.getName() = "down" or
  f.getName() = "down_interruptible" or
  f.getName() = "wait_event" or
  f.getName() = "wait_event_interruptible" or
  f.getName() = "wait_for_completion" or
  f.getName() = "might_sleep"
}

/* Predicate 4: caller is not atomic — i.e. its body contains a call to a
 * may-sleep function, OR it has might_sleep(), OR it does NOT contain any
 * atomic-context primitive (spin_lock, local_irq_save, rcu_read_lock). */
predicate caller_not_atomic(Function caller) {
  // Positive evidence: caller already calls something that requires sleepable ctx
  exists(FunctionCall fc2, Function callee2 |
    fc2.getEnclosingFunction() = caller and
    callee2 = fc2.getTarget() and
    func_may_sleep_in_caller(callee2)
  )
  or
  // Or: caller has no atomic-primitive call at all in its body
  not exists(FunctionCall fc3, Function callee3 |
    fc3.getEnclosingFunction() = caller and
    callee3 = fc3.getTarget() and
    (
      callee3.getName().matches("spin_lock%") or
      callee3.getName().matches("raw_spin_lock%") or
      callee3.getName().matches("read_lock%") or
      callee3.getName().matches("write_lock%") or
      callee3.getName() = "local_irq_save" or
      callee3.getName() = "local_irq_disable" or
      callee3.getName() = "preempt_disable" or
      callee3.getName() = "rcu_read_lock" or
      callee3.getName() = "rcu_read_lock_bh"
    )
  )
}

/* Predicate 5: the bug condition — GFP_ATOMIC at a call inside a non-atomic caller. */
predicate unnecessary_gfp_atomic(FunctionCall fc, Function caller, Function callee) {
  call_with_gfp_atomic(fc, callee, _) and
  caller = fc.getEnclosingFunction() and
  caller_not_atomic(caller) and
  // Filter to allocator/submission-like APIs whose 2nd-ish arg is gfp_t.
  (
    callee.getName() = "usb_submit_urb" or
    callee.getName() = "kmalloc" or
    callee.getName() = "kzalloc" or
    callee.getName() = "kcalloc" or
    callee.getName() = "kmalloc_array" or
    callee.getName() = "krealloc" or
    callee.getName() = "vmalloc" or
    callee.getName() = "vzalloc" or
    callee.getName() = "alloc_skb" or
    callee.getName() = "dev_alloc_skb" or
    callee.getName() = "netdev_alloc_skb" or
    callee.getName() = "__alloc_pages" or
    callee.getName() = "alloc_pages" or
    callee.getName() = "get_free_page" or
    callee.getName() = "__get_free_pages" or
    callee.getName().matches("kmem_cache_alloc%") or
    callee.getName() = "dma_alloc_coherent" or
    callee.getName() = "usb_alloc_coherent" or
    callee.getName() = "usb_alloc_urb"
  )
}

from FunctionCall fc, Function caller, Function callee
where unnecessary_gfp_atomic(fc, caller, callee)
select fc,
  "GFP_ATOMIC passed to " + callee.getName() + " but caller " + caller.getName() +
  " appears to run in non-atomic (sleepable) context; GFP_KERNEL likely suffices."
