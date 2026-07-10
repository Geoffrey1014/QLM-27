/**
 * @name of_node refcount leak in for_each_available_child_of_node early-exit (L0)
 * @description Detects functions where a for_each_available_child_of_node
 *   (or related of_node iterator macro) loop body contains a goto, return,
 *   or break with no preceding of_node_put() call between the loop start
 *   and the exit statement. Such early exits leak a reference on the
 *   iterator child node since the macro only auto-puts on natural loop
 *   completion. L0 ablation: N_PRED=1, all remaining logic merged into
 *   the assembly where-clause.
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3-l0-lin2-rep1-of-node-leak
 */
import cpp

predicate isForEachChildMacro(MacroInvocation mi) {
  mi.getMacroName() = "for_each_available_child_of_node" or
  mi.getMacroName() = "for_each_child_of_node" or
  mi.getMacroName() = "for_each_compatible_node" or
  mi.getMacroName() = "for_each_matching_node" or
  mi.getMacroName() = "for_each_node_by_name" or
  mi.getMacroName() = "for_each_node_by_type"
}

from ForStmt loop, MacroInvocation mi, Stmt exitStmt
where
  isForEachChildMacro(mi) and
  loop.getLocation().getFile() = mi.getFile() and
  loop.getLocation().getStartLine() = mi.getLocation().getStartLine() and
  loop.getLocation().getStartColumn() = mi.getLocation().getStartColumn() and
  exitStmt.getParentStmt+() = loop.getStmt() and
  (exitStmt instanceof GotoStmt or exitStmt instanceof ReturnStmt or exitStmt instanceof BreakStmt) and
  not exists(FunctionCall put |
    put.getTarget().getName() = "of_node_put" and
    put.getEnclosingFunction() = exitStmt.getEnclosingFunction() and
    put.getLocation().getStartLine() <= exitStmt.getLocation().getStartLine() and
    put.getLocation().getStartLine() >= loop.getLocation().getStartLine()
  )
select exitStmt, "of_node refcount leak: early exit inside " + mi.getMacroName() +
    " without of_node_put on iterator (function " +
    exitStmt.getEnclosingFunction().getName() + ")"
