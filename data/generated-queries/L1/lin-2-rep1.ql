/**
 * @name of_node refcount leak in for_each_available_child_of_node early-exit
 * @description Detects early exits (goto/return/break) from an of_node
 *   iterator macro loop body without a preceding of_node_put() on the
 *   iterator variable, leaking a refcount since the macro only auto-puts
 *   on natural loop completion.
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3-l1-lin2-rep1-of-node-leak
 */
import cpp

predicate isOfIteratorMacro(MacroInvocation mi) {
  mi.getMacroName() in [
      "for_each_available_child_of_node",
      "for_each_child_of_node",
      "for_each_compatible_node",
      "for_each_matching_node",
      "for_each_node_by_name",
      "for_each_node_by_type",
      "for_each_node_with_property"
    ]
}

predicate isOfNodePut(FunctionCall fc) {
  fc.getTarget().getName() = "of_node_put"
}

from ForStmt loop, MacroInvocation mi, Stmt exit
where
  isOfIteratorMacro(mi) and
  loop.getLocation().getFile() = mi.getFile() and
  loop.getLocation().getStartLine() = mi.getLocation().getStartLine() and
  exit.getParentStmt+() = loop.getStmt() and
  (exit instanceof GotoStmt or exit instanceof ReturnStmt or exit instanceof BreakStmt) and
  not exists(FunctionCall put |
    isOfNodePut(put) and
    put.getEnclosingFunction() = exit.getEnclosingFunction() and
    put.getLocation().getStartLine() <= exit.getLocation().getStartLine() and
    put.getLocation().getStartLine() >= loop.getLocation().getStartLine()
  )
select exit,
  "of_node refcount leak: early exit inside " + mi.getMacroName() +
    " without of_node_put (function " + exit.getEnclosingFunction().getName() + ")"
