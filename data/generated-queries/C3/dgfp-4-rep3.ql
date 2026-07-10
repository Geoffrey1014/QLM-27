/**
 * @name  GFP_ATOMIC used in sleepable initialization context (delay-gfp pattern)
 * @description Detects allocation / URB-submit calls passed GFP_ATOMIC inside
 *              a function whose name indicates a sleepable initialization /
 *              probe / setup / resume / suspend context, where the caller
 *              never runs in atomic context (no IRQ handler, no spinlock
 *              held, no IRQ-off section). Pattern derived from upstream
 *              commit 2453e60702e1 ("media: usb: em28xx: Replace GFP_ATOMIC
 *              with GFP_KERNEL in em28xx_init_usb_xfer()"), part of the
 *              Bai/DCNS delay-gfp findings family (ATC 2018 lineage).
 *
 *              The query gates on three predicates:
 *                P1. isAtomicAlloc           — the call site uses GFP_ATOMIC
 *                P2. inSleepableInitFunction — caller name is init/probe/setup/...
 *                P3. inAtomicContextByName   — caller name signals IRQ/ISR/tasklet
 *                P4. isLockHeldAroundCall    — a spinlock / IRQ-off appears before
 *                                              the call inside the same function
 *              accept iff P1 and P2 and not P3 and not P4
 *
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3/c3/delay-gfp-unneeded-atomic
 * @tags reliability
 *       delay-gfp
 *       performance
 */

import cpp

/* P1: an allocation / URB-submit call passed GFP_ATOMIC as its 2nd argument.
 *     The mini-DB POC defines GFP_ATOMIC as ((gfp_t)0x20u); CodeQL evaluates
 *     it to the constant 32. We also match the macro identifier in case the
 *     downstream Linux DB preserves the un-expanded source text. */
predicate isAtomicAlloc(FunctionCall fc) {
  (fc.getTarget().getName() = "usb_submit_urb" or
   fc.getTarget().getName() = "kzalloc" or
   fc.getTarget().getName() = "kmalloc" or
   fc.getTarget().getName() = "kcalloc" or
   fc.getTarget().getName() = "usb_alloc_urb") and
  exists(Expr arg | arg = fc.getArgument(1) |
    arg.toString().matches("%GFP_ATOMIC%") or
    arg.getValue().toInt() = 32
  )
}

/* P3: enclosing function name signals an atomic context (IRQ handler,
 *     ISR, tasklet, interrupt). Excluding these keeps the query silent on
 *     GFP_ATOMIC sites that are legitimately atomic. */
predicate inAtomicContextByName(Function f) {
  exists(string n |
    n = f.getName() |
    n.matches("%_isr%") or
    n.matches("%_irq_handler%") or
    n.matches("%irq_handler%") or
    n.matches("%_interrupt%") or
    n.matches("%_tasklet%")
  )
}

/* P4: a spinlock / IRQ-disable / preempt-disable / RCU read-lock call
 *     appears textually before `fc` inside the same function body. If so,
 *     the GFP_ATOMIC use is genuinely required by atomic-context rules. */
predicate isLockHeldAroundCall(FunctionCall fc) {
  exists(Function f, FunctionCall lockCall |
    f = fc.getEnclosingFunction() and
    lockCall.getEnclosingFunction() = f and
    (lockCall.getTarget().getName() = "spin_lock" or
     lockCall.getTarget().getName() = "spin_lock_irq" or
     lockCall.getTarget().getName() = "spin_lock_irqsave" or
     lockCall.getTarget().getName() = "spin_lock_bh" or
     lockCall.getTarget().getName() = "local_irq_save" or
     lockCall.getTarget().getName() = "local_irq_disable" or
     lockCall.getTarget().getName() = "preempt_disable" or
     lockCall.getTarget().getName() = "rcu_read_lock") and
    lockCall.getLocation().getStartLine() < fc.getLocation().getStartLine()
  )
}

/* P2: enclosing function looks like a sleepable entry point — driver
 *     init / probe / setup / resume / suspend. Combined with NOT-atomic
 *     above, this approximates "callable from process context only". */
predicate inSleepableInitFunction(Function f) {
  not inAtomicContextByName(f) and
  exists(string n |
    n = f.getName() |
    n.matches("%_init_%") or
    n.matches("%_init") or
    n.matches("%_probe%") or
    n.matches("%_setup%") or
    n.matches("%setup_%") or
    n.matches("%init_usb%") or
    n.matches("%device_init%") or
    n.matches("%_resume%") or
    n.matches("%_suspend%")
  )
}

from FunctionCall alloc, Function enc
where
  isAtomicAlloc(alloc) and
  enc = alloc.getEnclosingFunction() and
  inSleepableInitFunction(enc) and
  not inAtomicContextByName(enc) and
  not isLockHeldAroundCall(alloc)
select alloc,
  "GFP_ATOMIC used in sleepable initialization context '" + enc.getName() +
  "'; should be GFP_KERNEL."
