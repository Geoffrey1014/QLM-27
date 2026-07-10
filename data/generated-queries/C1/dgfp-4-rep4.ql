/**
 * @name GFP_ATOMIC used in a sleepable (process-context) function
 * @description Flags calls that pass `GFP_ATOMIC` as a gfp_t flag while
 *              executing in a function that strongly looks like a
 *              process / sleepable context (probe / init / open /
 *              suspend / resume / ioctl / mount / *_xfer helpers).
 *              In such contexts GFP_KERNEL is preferred: GFP_ATOMIC
 *              draws from the emergency reserves and is only needed
 *              when sleeping is forbidden (IRQ handler, spinlock
 *              held, etc.). Pattern source: DCNS (Bai et al.).
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-dgfp-4
 */

import cpp

/* ---------------------------------------------------------------------
 * GFP_ATOMIC literal recognition.
 *
 * GFP flags are #define macros; after the preprocessor we only see
 * integer literals, so we recognise the use via macro invocation
 * (Expr.isAffectedByMacro / MacroInvocation) — that survives the
 * extractor.
 * ------------------------------------------------------------------- */
predicate isGfpAtomicArg(Expr e) {
  exists(MacroInvocation mi |
    mi.getMacroName() = "GFP_ATOMIC" and
    mi.getExpr() = e
  )
}

/* ---------------------------------------------------------------------
 * Allocation / submission APIs whose last gfp_t argument we care about.
 * Listed by canonical kernel name; covers the GFP-flag-using APIs
 * exercised by the dgfp seeds.
 * ------------------------------------------------------------------- */
predicate isGfpApi(string name, int gfpArgIdx) {
  name = "usb_submit_urb"      and gfpArgIdx = 1
  or
  name = "kmalloc"             and gfpArgIdx = 1
  or
  name = "kzalloc"             and gfpArgIdx = 1
  or
  name = "kcalloc"             and gfpArgIdx = 2
  or
  name = "krealloc"            and gfpArgIdx = 2
  or
  name = "kmalloc_array"       and gfpArgIdx = 2
  or
  name = "kmemdup"             and gfpArgIdx = 2
  or
  name = "kstrdup"             and gfpArgIdx = 1
  or
  name = "vmalloc_node"        and gfpArgIdx = 2
  or
  name = "alloc_skb"           and gfpArgIdx = 1
  or
  name = "alloc_pages"         and gfpArgIdx = 0
  or
  name = "__get_free_pages"    and gfpArgIdx = 0
  or
  name = "dma_alloc_coherent"  and gfpArgIdx = 3
  or
  name = "dma_pool_alloc"      and gfpArgIdx = 1
  or
  name = "mempool_alloc"       and gfpArgIdx = 1
  or
  name = "sock_alloc_send_skb" and gfpArgIdx = 2
}

/* ---------------------------------------------------------------------
 * Sleepable-context heuristic — name-based. Kernel callbacks whose
 * names start/end with the listed tokens conventionally run in process
 * context (called from kthreads / sysfs / fs / driver core). The full
 * list mirrors what we use in dgfp-1/-2/-3 and works as a coarse
 * may-sleep filter without crossing call boundaries.
 * ------------------------------------------------------------------- */
predicate sleepableSuffix(string suf) {
  suf = "probe" or suf = "remove" or suf = "open" or suf = "release" or
  suf = "resume" or suf = "suspend" or suf = "init" or suf = "exit" or
  suf = "thread" or suf = "work" or suf = "workfn" or suf = "ioctl" or
  suf = "read" or suf = "write" or suf = "mount" or suf = "fill_super" or
  suf = "show" or suf = "store" or suf = "xfer" or suf = "start" or
  suf = "setup" or suf = "configure" or suf = "register" or suf = "load"
}

predicate inSleepableContext(Function f) {
  exists(string n, string suf |
    n = f.getName() and sleepableSuffix(suf) and
    (
      n = suf or
      n.matches("%_" + suf) or
      n.matches("%_" + suf + "_%") or
      n.matches(suf + "_%")
    )
  )
  or
  /* fallback: an independent call to a known sleeping primitive in
   * the same function corroborates may-sleep status. */
  exists(FunctionCall sc |
    sc.getEnclosingFunction() = f and
    (
      sc.getTarget().getName() = "msleep" or
      sc.getTarget().getName() = "msleep_interruptible" or
      sc.getTarget().getName() = "ssleep" or
      sc.getTarget().getName() = "usleep_range" or
      sc.getTarget().getName() = "mutex_lock" or
      sc.getTarget().getName() = "mutex_lock_interruptible" or
      sc.getTarget().getName() = "schedule_timeout" or
      sc.getTarget().getName() = "wait_event" or
      sc.getTarget().getName() = "wait_event_interruptible" or
      sc.getTarget().getName() = "wait_event_timeout" or
      sc.getTarget().getName() = "down" or
      sc.getTarget().getName() = "down_interruptible"
    )
  )
}

/* ---------------------------------------------------------------------
 * Atomic-context evidence: any call to a spinlock/irq/preempt
 * disabling primitive earlier in the same function makes a downstream
 * GFP_ATOMIC plausible and is suppressed.
 * ------------------------------------------------------------------- */
predicate hasAtomicCueBefore(Function f, FunctionCall target) {
  exists(FunctionCall atomic |
    atomic.getEnclosingFunction() = f and
    (
      atomic.getTarget().getName().matches("spin_lock%") or
      atomic.getTarget().getName().matches("raw_spin_lock%") or
      atomic.getTarget().getName().matches("_raw_spin_lock%") or
      atomic.getTarget().getName() = "local_irq_disable" or
      atomic.getTarget().getName() = "local_irq_save" or
      atomic.getTarget().getName() = "preempt_disable" or
      atomic.getTarget().getName() = "rcu_read_lock" or
      atomic.getTarget().getName() = "rcu_read_lock_bh" or
      atomic.getTarget().getName() = "read_lock" or
      atomic.getTarget().getName() = "write_lock"
    ) and
    atomic.getLocation().getStartLine() < target.getLocation().getStartLine()
  )
}

from FunctionCall call, Function fn, string api, int idx, Expr gfpArg, string msg
where
  api = call.getTarget().getName() and
  isGfpApi(api, idx) and
  gfpArg = call.getArgument(idx) and
  isGfpAtomicArg(gfpArg) and
  fn = call.getEnclosingFunction() and
  inSleepableContext(fn) and
  not hasAtomicCueBefore(fn, call) and
  msg = "Call to " + api +
        "() uses GFP_ATOMIC inside sleepable function '" + fn.getName() +
        "'; consider GFP_KERNEL."
select call, msg
