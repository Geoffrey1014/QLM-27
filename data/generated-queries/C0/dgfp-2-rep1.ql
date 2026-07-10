/**
 * @name Busy-wait mdelay used in sleepable (probe) context
 * @description Detects calls to mdelay() (and large udelay()) inside functions that
 *              are reachable from a driver .probe callback. Such call sites are not
 *              in atomic context, so the busy-wait should be replaced with msleep()
 *              or usleep_range() to avoid wasting CPU.
 * @kind problem
 * @problem.severity warning
 * @id cpp/busy-wait-in-probe-context
 * @tags efficiency
 *       correctness
 */

import cpp

/**
 * A call to a busy-wait delay routine that blocks the CPU for >= 10ms-equivalent.
 * mdelay(n) busy-waits n milliseconds.
 * udelay(n) busy-waits n microseconds; treat >=10000us (10ms) as a candidate.
 * ndelay(n) busy-waits n nanoseconds; treat >=10000000ns as a candidate.
 */
predicate isBusyWaitDelay(FunctionCall fc) {
  exists(string name | name = fc.getTarget().getName() |
    name = "mdelay"
    or
    (name = "udelay" and
      exists(int v | v = fc.getArgument(0).getValue().toInt() | v >= 1000))
    or
    (name = "ndelay" and
      exists(int v | v = fc.getArgument(0).getValue().toInt() | v >= 1000000))
  )
}

/**
 * A function that is assigned as the `.probe` member of a PCI/platform/USB/etc.
 * driver structure. These callbacks are always invoked in process (sleepable)
 * context by the driver core.
 */
predicate isProbeCallback(Function f) {
  exists(Initializer ini, Expr e |
    e = ini.getExpr().getAChild*() and
    e.(FunctionAccess).getTarget() = f
  ) and
  exists(VariableDeclarationEntry vde |
    vde.getDeclaration().getInitializer().getExpr().getAChild*().(FunctionAccess).getTarget() = f and
    vde.getType().getName().toLowerCase().matches("%driver%")
  )
}

/**
 * `callee` is transitively reachable from `caller` via direct calls.
 * Bounded to depth via standard `+` on the call graph.
 */
predicate reachableFrom(Function caller, Function callee) {
  caller.calls+(callee)
}

from FunctionCall delayCall, Function containing, Function probe
where
  isBusyWaitDelay(delayCall) and
  containing = delayCall.getEnclosingFunction() and
  isProbeCallback(probe) and
  (containing = probe or reachableFrom(probe, containing)) and
  // Exclude IRQ handlers and other atomic-context functions in the path: heuristic
  not containing.getName().toLowerCase().matches("%irq%") and
  not containing.getName().toLowerCase().matches("%isr%") and
  not containing.getName().toLowerCase().matches("%interrupt%")
select delayCall,
  "Busy-wait " + delayCall.getTarget().getName() +
    "() in function $@ is reachable from driver probe $@; consider msleep/usleep_range.",
  containing, containing.getName(), probe, probe.getName()
