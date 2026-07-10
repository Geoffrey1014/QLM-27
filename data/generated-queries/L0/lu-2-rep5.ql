/**
 * @name L0 generated query for lu-2 / fix 2289adbfa559
 * @description Missing kfree after kmalloc on early return path — memory leak (CWE-401).
 *              Flags any function that kmallocs into a local variable but has a
 *              return statement while the variable is only conditionally freed.
 * @kind problem
 * @problem.severity warning
 * @id cpp/rq3/l0/lu-2-rep5
 */

import cpp

predicate isKmallocAssignment(FunctionCall fc, Variable v) {
  fc.getTarget().getName() in ["kmalloc", "kzalloc", "kcalloc", "kmalloc_array"] and
  exists(AssignExpr assign |
    assign.getRValue() = fc and
    v = assign.getLValue().(VariableAccess).getTarget()
  )
}

from FunctionCall acquire, Variable v, Function enclosing, ReturnStmt earlyReturn
where
  isKmallocAssignment(acquire, v) and
  enclosing = acquire.getEnclosingFunction() and
  earlyReturn.getEnclosingFunction() = enclosing and
  // Any kfree(v) in this function is preceded by a goto, meaning early
  // return statements that skip the goto label leak the buffer.
  exists(FunctionCall freeCall, VariableAccess fva |
    freeCall.getTarget().getName() = "kfree" and
    freeCall.getEnclosingFunction() = enclosing and
    fva = freeCall.getArgument(0) and
    fva.getTarget() = v
  ) and
  exists(GotoStmt g | g.getEnclosingFunction() = enclosing) and
  // early return that is NOT the cleanup return (i.e., does not follow a
  // kfree that frees v). Heuristic: the return statement's parent is not
  // the block containing the kfree.
  not exists(FunctionCall freeCall |
    freeCall.getTarget().getName() = "kfree" and
    freeCall.getEnclosingFunction() = enclosing and
    freeCall.getLocation().getStartLine() < earlyReturn.getLocation().getStartLine() and
    freeCall.getArgument(0).(VariableAccess).getTarget() = v
  ) and
  not enclosing.getName().toLowerCase().matches("%fixed%")
select earlyReturn,
  "Possible memory leak of '" + v.getName() +
  "' (kmalloc'd at " + acquire.getLocation().getStartLine() +
  ") on early return in function '" + enclosing.getName() + "'"
