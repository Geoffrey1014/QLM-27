/**
 * @name GFP_ATOMIC used in sleepable context (delay-gfp pattern) [L0]
 * @description Detects allocation/URB-submission calls that pass GFP_ATOMIC
 *              while the enclosing function's name looks like a sleepable
 *              entry point (init/start/probe/resume/suspend/open) and does
 *              NOT look like an atomic entry point (irq/handler/atomic/
 *              completion/nmi/tasklet/critical/locked). Pattern from commit
 *              2453e60702e1 ("media: usb: em28xx: Replace GFP_ATOMIC with
 *              GFP_KERNEL in em28xx_init_usb_xfer()").
 *
 *              L0 zero-shot variant: exactly one helper predicate
 *              (isGfpAtomicCall recognises calls whose argument evaluates
 *              to 32, the numeric value of GFP_ATOMIC in the POC).
 *              Sleepable/atomic context tests are inlined in the
 *              assembly where-clause.
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3/l0/delay-gfp-gfp-atomic-in-sleepable
 * @tags reliability
 *       delay-gfp
 *       correctness
 */

import cpp

predicate isGfpAtomicCall(FunctionCall fc) {
  exists(Expr e | e = fc.getAnArgument() and e.getValue().toInt() = 32)
}

from FunctionCall fc, Function caller
where
  isGfpAtomicCall(fc) and
  caller = fc.getEnclosingFunction() and
  (caller.getName().matches("%init%") or
   caller.getName().matches("%start%") or
   caller.getName().matches("%probe%") or
   caller.getName().matches("%resume%") or
   caller.getName().matches("%suspend%") or
   caller.getName().matches("%open%")) and
  not (caller.getName().matches("%irq%") or
       caller.getName().matches("%handler%") or
       caller.getName().matches("%atomic%") or
       caller.getName().matches("%completion%") or
       caller.getName().matches("%nmi%") or
       caller.getName().matches("%tasklet%") or
       caller.getName().matches("%critical%") or
       caller.getName().matches("%locked%"))
select fc,
       "GFP_ATOMIC used in sleepable context (" + caller.getName() +
       "); consider GFP_KERNEL"
