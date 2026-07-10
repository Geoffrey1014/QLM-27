/**
 * @name  rq3-l0-dgfp-4-rep2
 * @id    cpp/rq3/l0/dgfp-4-rep2
 * @kind  problem
 * @problem.severity warning
 * @description Zero-shot compositional (L0) query for RQ4 delay-gfp pattern.
 *              Single predicate + assembly (no per-predicate refine, no
 *              assemble-refine). Detects usb_submit_urb() (and related
 *              helpers whose name contains `usb_submit_urb`) being called
 *              with GFP_ATOMIC inside a function whose name pattern places
 *              it on a sleepable context (init / probe / start / open /
 *              resume / suspend / work / thread / remove / shutdown /
 *              release / xfer / transfer), while excluding functions whose
 *              name pattern marks them as atomic-context (irq / isr /
 *              interrupt / tasklet / timer / nmi / atomic / handler /
 *              softirq / locked / callback).
 *              Seed: media: usb: em28xx commit 2453e60702e1 replaced
 *              GFP_ATOMIC with GFP_KERNEL inside em28xx_init_usb_xfer().
 */

import cpp

/**
 * Single L0 predicate: `fc` is a call to a function whose name contains
 * `usb_submit_urb`, and its second argument is the GFP_ATOMIC flag —
 * either the macro invocation (kernel build sees the macro) or its
 * expanded literal value 32 (the POC mini-DB has no kernel headers so
 * gcc substitutes the value before CodeQL sees the preprocessor record).
 */
predicate isUrbSubmitWithAtomic(FunctionCall fc) {
  fc.getTarget().getName().matches("%usb_submit_urb%") and
  (
    exists(MacroInvocation mi |
      mi.getMacroName() = "GFP_ATOMIC" and mi.getExpr() = fc.getArgument(1)
    )
    or
    fc.getArgument(1).(Literal).getValue() = "32"
  )
}

from FunctionCall fc, Function f
where
  isUrbSubmitWithAtomic(fc) and
  f = fc.getEnclosingFunction() and
  (f.getName().matches("%init%") or
   f.getName().matches("%probe%") or
   f.getName().matches("%start%") or
   f.getName().matches("%open%") or
   f.getName().matches("%resume%") or
   f.getName().matches("%suspend%") or
   f.getName().matches("%work%") or
   f.getName().matches("%thread%") or
   f.getName().matches("%remove%") or
   f.getName().matches("%shutdown%") or
   f.getName().matches("%release%") or
   f.getName().matches("%xfer%") or
   f.getName().matches("%transfer%")) and
  not (f.getName().matches("%irq%") or
       f.getName().matches("%isr%") or
       f.getName().matches("%interrupt%") or
       f.getName().matches("%tasklet%") or
       f.getName().matches("%timer%") or
       f.getName().matches("%nmi%") or
       f.getName().matches("%atomic%") or
       f.getName().matches("%handler%") or
       f.getName().matches("%softirq%") or
       f.getName().matches("%locked%") or
       f.getName().matches("%_cb") or
       f.getName().matches("%_callback%"))
select fc,
  "usb_submit_urb() called with GFP_ATOMIC inside sleepable context function '" +
  f.getName() + "'; consider replacing with GFP_KERNEL."
