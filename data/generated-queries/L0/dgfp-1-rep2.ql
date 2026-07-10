/**
 * @name mdelay() in sleepable kernel callback (delay-gfp pattern)
 * @description Detects mdelay() busy-wait calls inside functions whose
 *              names indicate a sleepable execution context (PM callbacks,
 *              probe/remove, module init, workqueue handlers, kernel
 *              threads, char-device open/release). Such call sites should
 *              use msleep() instead so the CPU is not tied up.
 * @kind problem
 * @problem.severity warning
 * @id qlm/l0-dgfp1-mdelay-in-sleepable-callback
 */
import cpp

predicate isMdelayInSleepableCallback(FunctionCall fc) {
  fc.getTarget().getName() = "mdelay" and
  exists(Function f |
    f = fc.getEnclosingFunction() and
    (
      f.getName().matches("%_resume") or
      f.getName().matches("%_suspend") or
      f.getName().matches("%_probe") or
      f.getName().matches("%_remove") or
      f.getName().matches("%_init") or
      f.getName().matches("%_worker") or
      f.getName().matches("%_work") or
      f.getName().matches("%_thread") or
      f.getName().matches("%_open") or
      f.getName().matches("%_release")
    )
  )
}

from FunctionCall fc, Function f
where isMdelayInSleepableCallback(fc)
  and f = fc.getEnclosingFunction()
select fc,
  "mdelay() called in likely-sleepable function '" + f.getName() +
  "' - consider replacing with msleep()."
