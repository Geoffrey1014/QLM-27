/**
 * @name C3 generated query for lin-3 / fix bf4a9b2467b7
 * @description Missing of_node_put after of_parse_phandle on error path —
 *              device_node refcount leak (CWE-911).
 * @kind problem
 * @problem.severity warning
 * @id cpp/rq3/c3/lin-3-rep4
 */

import cpp

predicate isDeviceNodeAcquisition(FunctionCall fc) {
  fc.getTarget().getName() in [
    "of_parse_phandle",
    "of_find_node_by_name",
    "of_find_node_by_path",
    "of_get_child_by_name",
    "of_find_compatible_node"
  ]
}

predicate isOfNodePut(FunctionCall fc) {
  fc.getTarget().getName() = "of_node_put"
}

Variable getAcquiredVariable(FunctionCall acquire) {
  exists(AssignExpr assign |
    assign.getRValue() = acquire and
    result = assign.getLValue().(VariableAccess).getTarget()
  )
}

predicate hasMatchingOfNodePut(FunctionCall acquire, Variable v) {
  exists(FunctionCall putCall |
    isOfNodePut(putCall) and
    putCall.getEnclosingFunction() = acquire.getEnclosingFunction() and
    exists(VariableAccess va |
      va = putCall.getArgument(0) and
      va.getTarget() = v
    )
  )
}

/**
 * True iff there is a ReturnStmt after `acquire` in the same function
 * such that no `of_node_put(v)` call occurs between `acquire` and that
 * return statement (line-number ordering, intraprocedural).
 */
predicate hasErrorReturnBeforePut(FunctionCall acquire, Variable v) {
  exists(ReturnStmt r |
    r.getEnclosingFunction() = acquire.getEnclosingFunction() and
    r.getLocation().getStartLine() > acquire.getLocation().getStartLine() and
    not exists(FunctionCall p |
      isOfNodePut(p) and
      p.getEnclosingFunction() = acquire.getEnclosingFunction() and
      exists(VariableAccess va |
        va = p.getArgument(0) and
        va.getTarget() = v
      ) and
      p.getLocation().getStartLine() < r.getLocation().getStartLine() and
      p.getLocation().getStartLine() > acquire.getLocation().getStartLine()
    )
  )
}

predicate isInFixedFunction(FunctionCall fc) {
  fc.getEnclosingFunction().getName().toLowerCase().matches("%fixed%") or
  fc.getEnclosingFunction().getName().toLowerCase().matches("%_fp%")
}

from FunctionCall acquire, Variable acquiredVar
where
  isDeviceNodeAcquisition(acquire) and
  acquiredVar = getAcquiredVariable(acquire) and
  hasErrorReturnBeforePut(acquire, acquiredVar) and
  not isInFixedFunction(acquire)
select acquire,
  "Call to " + acquire.getTarget().getName() +
    " stores result in '" + acquiredVar.getName() +
    "' but no of_node_put() precedes a subsequent return; device_node refcount leak."
