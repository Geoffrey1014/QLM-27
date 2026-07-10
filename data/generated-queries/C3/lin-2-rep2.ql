/**
 * @name C3 generated query for lin-2 / fix 9a2ea132df86
 * @description Missing of_node_put on early-exit from for_each_available_child_of_node
 *              loop — device_node refcount leak (CWE-911).
 * @kind problem
 * @problem.severity warning
 * @id cpp/rq3/c3/lin-2-rep2
 */

import cpp

predicate isForEachChildLoop(ForStmt loop, Variable child) {
  exists(FunctionCall fc |
    fc.getTarget().getName() = "__first_child" and
    fc.getEnclosingStmt() = loop.getInitialization() and
    exists(AssignExpr ae, VariableAccess va |
      ae.getRValue() = fc and
      va = ae.getLValue() and
      va.getTarget() = child
    )
  )
}

predicate isOfNodePutOn(FunctionCall put, Variable v) {
  put.getTarget().getName() = "of_node_put" and
  exists(VariableAccess va |
    va = put.getArgument(0) and
    va.getTarget() = v
  )
}

predicate isEarlyExit(Stmt s, ForStmt loop) {
  (s instanceof GotoStmt or s instanceof ReturnStmt) and
  loop.getStmt().getAChild*() = s
}

predicate earlyExitMissingPut(ForStmt loop, Variable child, Stmt exit) {
  isForEachChildLoop(loop, child) and
  isEarlyExit(exit, loop) and
  not exists(FunctionCall put |
    isOfNodePutOn(put, child) and
    put.getEnclosingFunction() = loop.getEnclosingFunction()
  )
}

predicate isInFixedFunction(ForStmt loop) {
  loop.getEnclosingFunction().getName().toLowerCase().matches("%fixed%")
}

from ForStmt loop, Variable child, Stmt exit
where
  earlyExitMissingPut(loop, child, exit) and
  not isInFixedFunction(loop)
select loop,
  "for_each_*_child_of_node loop early-exits via $@ without of_node_put('" +
    child.getName() + "'), causing a device_node refcount leak",
  exit, exit.toString()
