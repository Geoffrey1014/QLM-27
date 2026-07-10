/**
 * @name of_node refcount leak in for_each_available_child_of_node early-exit
 * @description Detects functions where a for_each_available_child_of_node
 *   (or related of_node iterator macro) loop body contains a goto, return,
 *   or break with no preceding of_node_put() call in the same function.
 *   Such early exits leak a reference on the iterator child node since the
 *   macro only auto-puts on natural loop completion.
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3-c3-lin2-rep1-of-node-leak
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

predicate isOfNodePutCall(FunctionCall fc) {
  fc.getTarget().getName() = "of_node_put"
}

/* A ForStmt whose start position matches an of_node iterator macro
 * invocation site in the same file. */
predicate isOfIteratorForLoop(ForStmt loop, MacroInvocation mi) {
  isForEachChildMacro(mi) and
  loop.getLocation().getFile() = mi.getFile() and
  loop.getLocation().getStartLine() = mi.getLocation().getStartLine() and
  loop.getLocation().getStartColumn() = mi.getLocation().getStartColumn()
}

/* The for-loop body contains a goto, return, or break that breaks out
 * of the iteration without calling of_node_put earlier in the function. */
predicate loopHasUnguardedEarlyExit(ForStmt loop, MacroInvocation mi, Stmt exitStmt) {
  isOfIteratorForLoop(loop, mi) and
  exitStmt.getParentStmt+() = loop.getStmt() and
  (exitStmt instanceof GotoStmt or exitStmt instanceof ReturnStmt or exitStmt instanceof BreakStmt) and
  not exists(FunctionCall put |
    isOfNodePutCall(put) and
    put.getEnclosingFunction() = exitStmt.getEnclosingFunction() and
    put.getLocation().getStartLine() <= exitStmt.getLocation().getStartLine() and
    put.getLocation().getStartLine() >= loop.getLocation().getStartLine()
  )
}

from ForStmt loop, MacroInvocation mi, Stmt exitStmt
where loopHasUnguardedEarlyExit(loop, mi, exitStmt)
select exitStmt, "of_node refcount leak: early exit inside " + mi.getMacroName() +
    " without of_node_put on iterator (function " +
    exitStmt.getEnclosingFunction().getName() + ")"
