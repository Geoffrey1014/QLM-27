/**
 * @name of_node refcount leak in for_each_available_child_of_node early-exit
 * @description Detects functions where a for_each_available_child_of_node
 *   (or related of_node iterator macro) loop body contains a goto, return,
 *   or break with no preceding of_node_put() call in the same function.
 *   Such early exits leak a reference on the iterator child node since the
 *   macro only auto-puts on natural loop completion.
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3-l0-lin2-rep5-of-node-leak
 */
import cpp

predicate isOfIteratorForLoop(ForStmt loop, MacroInvocation mi) {
  (mi.getMacroName() = "for_each_available_child_of_node" or
   mi.getMacroName() = "for_each_child_of_node" or
   mi.getMacroName() = "for_each_compatible_node" or
   mi.getMacroName() = "for_each_matching_node" or
   mi.getMacroName() = "for_each_node_by_name" or
   mi.getMacroName() = "for_each_node_by_type") and
  loop.getLocation().getFile() = mi.getFile() and
  loop.getLocation().getStartLine() = mi.getLocation().getStartLine()
}

from ForStmt loop, MacroInvocation mi, Stmt exitStmt
where isOfIteratorForLoop(loop, mi) and
      exitStmt.getParentStmt+() = loop.getStmt() and
      (exitStmt instanceof GotoStmt or
       exitStmt instanceof ReturnStmt or
       exitStmt instanceof BreakStmt) and
      not exists(FunctionCall put |
        put.getTarget().getName() = "of_node_put" and
        put.getEnclosingFunction() = exitStmt.getEnclosingFunction() and
        put.getLocation().getStartLine() <= exitStmt.getLocation().getStartLine() and
        put.getLocation().getStartLine() >= loop.getLocation().getStartLine()
      )
select exitStmt, "of_node refcount leak: early exit inside " + mi.getMacroName() +
       " without of_node_put on iterator (function " +
       exitStmt.getEnclosingFunction().getName() + ")"
