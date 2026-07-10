/**
 * @name of_node refcount leak in for_each_available_child_of_node loop
 * @description Detects functions that use the for_each_available_child_of_node
 *              macro and exit the loop early via goto without releasing the
 *              child device_node reference via of_node_put. Pattern derived
 *              from Linux commit 9a2ea132df86 (HSI: omap_ssi: Fix refcount
 *              leak in ssi_probe). CWE-911.
 * @kind problem
 * @problem.severity warning
 * @id cpp/rq3/c3/lin-2-rep4
 */

import cpp

predicate isForEachAvailableChildMacro(MacroInvocation mi) {
  mi.getMacroName() = "for_each_available_child_of_node"
}

predicate functionCallsOfNodePut(Function f) {
  exists(FunctionCall c |
    c.getEnclosingFunction() = f and
    c.getTarget().getName() = "of_node_put"
  )
}

predicate hasEarlyExitAfterMacro(MacroInvocation mi, Stmt exit) {
  isForEachAvailableChildMacro(mi) and
  exit.getEnclosingFunction() = mi.getEnclosingFunction() and
  (exit instanceof GotoStmt or exit instanceof ReturnStmt or exit instanceof BreakStmt) and
  exit.getLocation().getStartLine() > mi.getLocation().getStartLine()
}

predicate isBuggyForEachLeak(MacroInvocation mi, Function f) {
  isForEachAvailableChildMacro(mi) and
  f = mi.getEnclosingFunction() and
  exists(GotoStmt g |
    g.getEnclosingFunction() = f and
    g.getLocation().getStartLine() > mi.getLocation().getStartLine()
  ) and
  not functionCallsOfNodePut(f)
}

from MacroInvocation mi, Function f
where isBuggyForEachLeak(mi, f)
select mi,
  "of_node refcount leak: function '" + f.getName() +
    "' uses for_each_available_child_of_node and exits early via goto " +
    "without calling of_node_put on the child loop variable (CWE-911)."
