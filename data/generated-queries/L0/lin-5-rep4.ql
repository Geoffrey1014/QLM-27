/**
 * @name L0 generated query for lin-5 / fix 10d6bdf53290
 * @description Missing put_device after of_find_device_by_node — struct device
 *              refcount leak in ata: pata_octeon_cf (CWE-772)
 * @kind problem
 * @problem.severity warning
 * @id cpp/rq3/l0/lin-5-rep4
 */

import cpp

predicate isDeviceAcquisition(FunctionCall fc) {
  fc.getTarget().getName() = "of_find_device_by_node"
}

from FunctionCall acquire, Variable v
where
  isDeviceAcquisition(acquire) and
  exists(AssignExpr assign |
    assign.getRValue() = acquire and
    v = assign.getLValue().(VariableAccess).getTarget()
  ) and
  exists(IfStmt ifStmt, VariableAccess va |
    ifStmt.getEnclosingFunction() = acquire.getEnclosingFunction() and
    va.getTarget() = v and
    ifStmt.getCondition().getAChild*() = va
  ) and
  not exists(FunctionCall putCall, FieldAccess fa, VariableAccess va |
    putCall.getTarget().getName() = "put_device" and
    putCall.getEnclosingFunction() = acquire.getEnclosingFunction() and
    (
      putCall.getArgument(0) = fa and
      fa.getQualifier() = va and
      va.getTarget() = v
      or
      exists(AddressOfExpr aoe |
        putCall.getArgument(0) = aoe and
        aoe.getOperand() = fa and
        fa.getQualifier() = va and
        va.getTarget() = v
      )
    )
  ) and
  not acquire.getEnclosingFunction().getName().toLowerCase().matches("%fixed%")
select acquire,
  "Call to " + acquire.getTarget().getName() +
    " stores result in '" + v.getName() +
    "' but put_device() is never called on it, causing a device refcount leak"
