/**
 * @name Missing of_node_put after of_parse_phandle
 * @description Detects missing of_node_put calls after of_parse_phandle, which can cause device node reference count leaks (CWE-401)
 * @kind problem
 * @problem.severity warning
 * @id cpp/missing-of-node-put
 */

import cpp

/**
 * Identifies calls to of_parse_phandle and similar functions that return
 * a device_node with an incremented reference count
 */
predicate isDeviceNodeAcquisition(FunctionCall fc) {
  fc.getTarget().getName() in [
    "of_parse_phandle",
    "of_find_node_by_name",
    "of_find_node_by_path",
    "of_get_child_by_name",
    "of_find_compatible_node"
  ]
}

/**
 * Identifies calls to of_node_put which releases the reference count
 */
predicate isOfNodePut(FunctionCall fc) {
  fc.getTarget().getName() = "of_node_put"
}

/**
 * Gets the variable that stores the result of the acquisition call
 */
Variable getAcquiredVariable(FunctionCall acquire) {
  exists(AssignExpr assign |
    assign.getRValue() = acquire and
    result = assign.getLValue().(VariableAccess).getTarget()
  )
}

/**
 * Checks if there's an of_node_put call on the same variable in the same function
 */
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
 * Checks if the acquisition is in a loop (where the bug pattern typically occurs)
 */
predicate isInLoop(FunctionCall fc) {
  exists(Loop loop |
    loop.getAChild*() = fc
  )
}

/**
 * Checks if there's a null check on the variable (indicating the value is used)
 */
predicate hasNullCheck(FunctionCall acquire, Variable v) {
  exists(IfStmt ifStmt, VariableAccess va |
    ifStmt.getEnclosingFunction() = acquire.getEnclosingFunction() and
    va.getTarget() = v and
    ifStmt.getCondition().getAChild*() = va
  )
}

/**
 * Identifies functions that appear to be fixed versions (for filtering)
 */
predicate isInFixedFunction(FunctionCall fc) {
  fc.getEnclosingFunction().getName().toLowerCase().matches("%fixed%")
}

from FunctionCall acquire, Variable acquiredVar
where
  isDeviceNodeAcquisition(acquire) and
  acquiredVar = getAcquiredVariable(acquire) and
  // The variable is used (has a null check or other use)
  hasNullCheck(acquire, acquiredVar) and
  // No matching of_node_put call found
  not hasMatchingOfNodePut(acquire, acquiredVar) and
  // Exclude fixed versions
  not isInFixedFunction(acquire)
select acquire,
  "Call to " + acquire.getTarget().getName() +
    " stores result in '" + acquiredVar.getName() +
    "' but of_node_put() is never called, causing a device node reference count leak"