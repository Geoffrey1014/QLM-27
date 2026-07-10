/**
 * @name  rq3-c3-dgfp-4-rep2
 * @id    cpp/rq3/c3/dgfp-4-rep2
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-ON generation for RQ3 cell C3.
 *              Detects usb_submit_urb() (and related helpers ending in
 *              `usb_submit_urb`) being called with GFP_ATOMIC inside a
 *              function whose name pattern places it on a sleepable
 *              context (init / probe / start / open / resume / suspend
 *              / work / thread / remove / shutdown / release / xfer /
 *              transfer), while excluding functions whose name pattern
 *              marks them as atomic-context (irq / isr / interrupt /
 *              tasklet / timer / nmi / atomic / handler / softirq /
 *              locked / callback). Seed: media: usb: em28xx commit
 *              2453e60702e1 replaced GFP_ATOMIC with GFP_KERNEL inside
 *              em28xx_init_usb_xfer().
 */

import cpp

/**
 * Holds if `e` is the `GFP_ATOMIC` flag — either as a macro invocation
 * (preferred, kernel build sees the macro) or as its expanded literal
 * value 32 (the POC mini-DB has no kernel headers so the macro is
 * substituted by gcc before the preprocessor record reaches CodeQL).
 */
predicate isGfpAtomicMacro(Expr e) {
  exists(MacroInvocation mi |
    mi.getMacroName() = "GFP_ATOMIC" and mi.getExpr() = e
  )
  or
  e.(Literal).getValue() = "32"
}

/**
 * Holds if `fc` is a call to a function whose name ends in
 * `usb_submit_urb` (canonical kernel API plus any local helper named
 * `*usb_submit_urb*`) and its second argument is GFP_ATOMIC.
 */
predicate isUrbSubmitWithAtomic(FunctionCall fc) {
  fc.getTarget().getName().matches("%usb_submit_urb%") and
  isGfpAtomicMacro(fc.getArgument(1))
}

/**
 * Holds if `f` looks like a function that runs in a sleepable
 * (non-atomic) context based on its name. Covers PCI/platform probe,
 * driver init, streaming start, file open/release, suspend/resume,
 * workqueue/thread bodies, and remove/shutdown teardown — all of
 * which are the usual non-atomic call paths in Linux drivers.
 */
predicate inSleepableContextByName(Function f) {
  exists(string n | n = f.getName() |
    n.matches("%init%") or n.matches("%probe%") or n.matches("%start%") or
    n.matches("%open%") or n.matches("%resume%") or n.matches("%suspend%") or
    n.matches("%work%") or n.matches("%thread%") or n.matches("%remove%") or
    n.matches("%shutdown%") or n.matches("%release%") or n.matches("%xfer%") or
    n.matches("%transfer%")
  )
}

/**
 * Holds if `f` is plausibly an atomic-context function we should NOT
 * flag: hard/soft IRQ handlers, tasklets, NMI paths, anything named
 * `*_locked`, generic `*_cb` / `*_callback` callbacks.
 */
predicate inAtomicContextByName(Function f) {
  exists(string n | n = f.getName() |
    n.matches("%irq%") or n.matches("%isr%") or n.matches("%interrupt%") or
    n.matches("%tasklet%") or n.matches("%timer%") or n.matches("%nmi%") or
    n.matches("%atomic%") or n.matches("%handler%") or n.matches("%softirq%") or
    n.matches("%locked%") or n.matches("%_cb") or n.matches("%_callback%")
  )
}

/**
 * The composed predicate: `fc` is a `usb_submit_urb(...,GFP_ATOMIC)`
 * call whose enclosing function `f` is name-shape sleepable and not
 * name-shape atomic. This is the dgfp-relaxation signal: in such
 * contexts `GFP_KERNEL` is the correct flag.
 */
predicate atomicGfpInSleepableSubmit(FunctionCall fc, Function f) {
  isUrbSubmitWithAtomic(fc) and
  f = fc.getEnclosingFunction() and
  inSleepableContextByName(f) and
  not inAtomicContextByName(f)
}

from FunctionCall fc, Function f
where atomicGfpInSleepableSubmit(fc, f)
select fc,
  "usb_submit_urb() called with GFP_ATOMIC inside sleepable context function '" +
  f.getName() + "'; consider replacing with GFP_KERNEL."
