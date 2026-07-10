/**
 * @name delay-gfp: mdelay in likely-sleepable context
 * @description Flags calls to mdelay() inside functions whose names indicate
 *              a sleepable execution context (e.g. *_init, *_probe, *_open,
 *              *_ioctl, *_resume, *_suspend, *_release). Such busy-waits
 *              should typically be replaced with msleep() to avoid wasting
 *              CPU cycles.
 * @kind problem
 * @problem.severity warning
 * @id cpp/qlllm-rq3-d5-l0-dgfp-2-rep3
 * @tags performance
 *       correctness
 */

import cpp

predicate isMdelayCall(FunctionCall fc) { fc.getTarget().getName() = "mdelay" }

from FunctionCall fc, Function enc
where
  isMdelayCall(fc) and
  enc = fc.getEnclosingFunction() and
  (
    enc.getName().matches("%_init%") or
    enc.getName().matches("%_probe%") or
    enc.getName().matches("%_open%") or
    enc.getName().matches("%_resume%") or
    enc.getName().matches("%_suspend%") or
    enc.getName().matches("%_ioctl%") or
    enc.getName().matches("%_release%")
  )
select fc,
  "mdelay() called in likely-sleepable context (" + enc.getName() +
    "); consider msleep()."
