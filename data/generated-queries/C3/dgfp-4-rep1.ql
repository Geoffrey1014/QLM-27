/**
 * @name  GFP_ATOMIC in sleepable context (delay-gfp pattern)
 * @description Detects calls passing GFP_ATOMIC whose enclosing function
 *              runs in sleepable / process context (init / start_streaming
 *              / start_feed / probe / resume / suspend / xfer / work),
 *              where GFP_KERNEL is the correct flag and lets the allocator
 *              sleep instead of tapping the small atomic reserve. Pattern
 *              derived from upstream commit 2453e60702e1 ("media: usb:
 *              em28xx: Replace GFP_ATOMIC with GFP_KERNEL in
 *              em28xx_init_usb_xfer()"), a Bai/DCNS-style delay-gfp
 *              finding (ATC 2018 family).
 *
 *              The query gates on:
 *                P1. a call site whose argument list contains GFP_ATOMIC
 *                    (matched both by literal value 32 and by macro name).
 *                P2. the enclosing function name matches a sleepable shape
 *                    (init/probe/resume/suspend/start_streaming/start_feed/
 *                    xfer/work).
 *                P3. the enclosing function does NOT match an atomic shape
 *                    (irq/handler/isr/interrupt/completion/critical_section)
 *                    and does NOT call any spin_lock variant, preempt_disable,
 *                    local_irq_disable, or rcu_read_lock — these are where
 *                    GFP_ATOMIC is genuinely required.
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3/c3/delay-gfp-gfpatomic-in-sleepable
 * @tags reliability
 *       delay-gfp
 *       performance
 */

import cpp

/* P1: a call site that passes GFP_ATOMIC as one of its arguments.
 *     We match by literal int value (32 = the actual numeric value of
 *     GFP_ATOMIC after macro expansion in the kernel headers) and also
 *     by the spelled token "GFP_ATOMIC" for source bases where the
 *     macro has not been expanded by the extractor. */
predicate isGfpAtomicCall(FunctionCall fc) {
  exists(Expr arg | arg = fc.getAnArgument() |
    arg.getValue().toInt() = 32 or arg.toString() = "GFP_ATOMIC"
  )
}

/* P3-helper: enclosing function looks atomic — IRQ/ISR handler, NMI,
 *     completion callback, OR holds a spinlock / has preemption disabled
 *     / is inside RCU read-side. GFP_ATOMIC is appropriate here, so the
 *     query MUST stay silent. */
predicate isAtomicContextFunction(Function f) {
  f.getName().matches("%_irq_handler%") or
  f.getName().matches("%_isr%") or
  f.getName().matches("%_interrupt%") or
  f.getName().matches("%irq_handler%") or
  f.getName().matches("%_completion%") or
  f.getName().matches("%completion_%") or
  f.getName().matches("%critical_section%") or
  exists(FunctionCall fc |
    fc.getEnclosingFunction() = f and
    (
      fc.getTarget().getName() = "spin_lock" or
      fc.getTarget().getName() = "spin_lock_irq" or
      fc.getTarget().getName() = "spin_lock_irqsave" or
      fc.getTarget().getName() = "spin_lock_bh" or
      fc.getTarget().getName() = "local_irq_disable" or
      fc.getTarget().getName() = "preempt_disable" or
      fc.getTarget().getName() = "rcu_read_lock"
    )
  )
}

/* P2: enclosing function looks sleepable — PM resume/suspend callbacks,
 *     driver probe, *_init helpers, V4L2 .start_streaming, DVB
 *     .start_feed, USB *_xfer wrappers, workqueue handlers. GFP_KERNEL
 *     is correct in these. P3-helper negated to filter out names that
 *     simultaneously look atomic (e.g. "init_irq_handler"). */
predicate isSleepableContextFunction(Function f) {
  not isAtomicContextFunction(f) and
  (
    f.getName().matches("%_probe%") or
    f.getName().matches("%_init%") or
    f.getName().matches("%_init_%") or
    f.getName().matches("%_resume%") or
    f.getName().matches("%_suspend%") or
    f.getName().matches("%_start_streaming%") or
    f.getName().matches("%start_streaming%") or
    f.getName().matches("%_start_feed%") or
    f.getName().matches("%start_feed%") or
    f.getName().matches("%_xfer%") or
    f.getName().matches("%_work%")
  )
}

/* Top-level combinator: GFP_ATOMIC call site inside a sleepable callee. */
predicate gfpAtomicInSleepableContext(FunctionCall fc) {
  isGfpAtomicCall(fc) and
  isSleepableContextFunction(fc.getEnclosingFunction())
}

from FunctionCall fc, Function caller
where
  gfpAtomicInSleepableContext(fc) and
  caller = fc.getEnclosingFunction()
select fc,
       "GFP_ATOMIC passed to " + fc.getTarget().getName() +
       "() in sleepable context (" + caller.getName() +
       "); should be GFP_KERNEL."
