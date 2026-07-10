/**
 * @name Missing of_node_put on early exit from for_each_available_child_of_node
 * @description Detects refcount leaks where control flow (goto/return/break)
 *              leaves a for_each_available_child_of_node loop body without
 *              first calling of_node_put on the loop variable.
 *              Pattern origin: HSI: omap_ssi: Fix refcount leak in ssi_probe
 *              (9a2ea132df86).
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3-l0-lin-2
 */

import cpp

predicate isForEachAvailableChildLoop(ForStmt fs, Variable child) {
  exists(FunctionCall init |
    init = fs.getInitialization().(ExprStmt).getExpr().(AssignExpr).getRValue() and
    init.getTarget().getName() = "of_get_next_available_child"
  ) and
  child.getAnAccess() = fs.getInitialization().(ExprStmt).getExpr().(AssignExpr).getLValue()
}

from ForStmt loop, Variable child, Stmt exit
where
  isForEachAvailableChildLoop(loop, child) and
  (exit instanceof GotoStmt or exit instanceof ReturnStmt or exit instanceof BreakStmt) and
  loop.getStmt().getAChild*() = exit and
  not exists(FunctionCall put |
    put.getTarget().getName() = "of_node_put" and
    put.getArgument(0).(VariableAccess).getTarget() = child and
    loop.getStmt().getAChild*() = put.getEnclosingStmt() and
    put.getLocation().getEndLine() < exit.getLocation().getStartLine()
  )
select exit,
  "missing of_node_put(" + child.getName() +
    ") before early exit from for_each_available_child_of_node loop"
