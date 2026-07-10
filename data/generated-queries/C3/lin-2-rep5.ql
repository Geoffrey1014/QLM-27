/**
 * @name C3 generated query for lin-2 / fix 9a2ea132df86
 * @description Missing of_node_put on early exit from for_each_available_child_of_node loop
 * @kind problem
 * @problem.severity warning
 * @id cpp/rq3/c3/lin-2-rep5
 */

import cpp

predicate isForEachChildLoop(ForStmt fs, Variable child) {
  exists(FunctionCall fc |
    fc.getParent*() = fs.getUpdate() and
    fc.getTarget().getName() = "__next_child"
  ) and
  exists(AssignExpr ae, FunctionCall init |
    ae.getParent*() = fs.getInitialization() and
    init.getTarget().getName() = "__first_child" and
    ae.getRValue() = init and
    ae.getLValue().(VariableAccess).getTarget() = child
  )
}

predicate isOfNodePut(FunctionCall fc) {
  fc.getTarget().getName() = "of_node_put"
}

predicate hasOfNodePutBefore(Stmt exit, Variable child, ForStmt fs) {
  exists(FunctionCall put |
    isOfNodePut(put) and
    put.getArgument(0).(VariableAccess).getTarget() = child and
    put.getEnclosingStmt().getParent*() = fs.getStmt() and
    put.getLocation().getStartLine() < exit.getLocation().getStartLine() and
    put.getLocation().getStartLine() >= fs.getLocation().getStartLine()
  )
}

predicate isEarlyExit(Stmt s) {
  s instanceof GotoStmt or
  s instanceof ReturnStmt or
  (s instanceof BreakStmt and not exists(SwitchStmt sw | s.getParent*() = sw))
}

predicate hasEarlyExitWithoutPut(ForStmt fs, Variable child, Stmt exit) {
  isForEachChildLoop(fs, child) and
  exit.getParent*() = fs.getStmt() and
  isEarlyExit(exit) and
  not hasOfNodePutBefore(exit, child, fs)
}

from ForStmt fs, Variable child, Stmt exit
where
  hasEarlyExitWithoutPut(fs, child, exit)
select exit,
  "Early exit from for_each_available_child_of_node loop without of_node_put('" +
  child.getName() + "') — device_node reference count leak"
