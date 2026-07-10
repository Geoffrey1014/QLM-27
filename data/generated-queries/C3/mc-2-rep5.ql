/**
 * @name C3 generated query for mc-2 / fix 09acf29c8246
 * @description Missing NULL check after kzalloc — NULL pointer dereference (CWE-476)
 * @kind problem
 * @problem.severity warning
 * @id cpp/rq3/c3/mc-2-rep5
 */

import cpp

predicate isAllocCall(FunctionCall fc) {
  fc.getTarget().getName() in ["kzalloc", "kmalloc", "kcalloc"]
}

predicate isInFixedFunction(FunctionCall fc) {
  fc.getEnclosingFunction().getName().toLowerCase().matches("%fixed%") or
  fc.getEnclosingFunction().getName().toLowerCase().matches("%_tn%")
}

predicate isInFpFunction(FunctionCall fc) {
  fc.getEnclosingFunction().getName().toLowerCase().matches("%_fp%")
}

predicate isResultDereferenced(FunctionCall acquire) {
  // Direct pointer-field-access dereference of the assigned variable/field
  exists(PointerFieldAccess deref |
    deref.getEnclosingFunction() = acquire.getEnclosingFunction() and
    (
      // Local variable via assignment: fw = kzalloc(...); fw->...
      exists(AssignExpr a, VariableAccess va |
        a.getRValue() = acquire and
        va.getTarget() = a.getLValue().(VariableAccess).getTarget() and
        deref.getQualifier() = va
      )
      or
      // Local variable via initializer: struct X *fw = kzalloc(...); fw->...
      exists(Variable v, VariableAccess va |
        v.getInitializer().getExpr() = acquire and
        va.getTarget() = v and
        deref.getQualifier() = va
      )
      or
      // Struct field case: priv->pFirmware = kzalloc(...); priv->pFirmware->...
      exists(AssignExpr a, PointerFieldAccess lhs, PointerFieldAccess use |
        a.getRValue() = acquire and
        lhs = a.getLValue() and
        use = deref.getQualifier() and
        use.getTarget() = lhs.getTarget()
      )
    )
  )
  or
  // Passed as argument to another function (likely dereferenced there)
  // Excludes free-like sinks
  exists(FunctionCall use, VariableAccess va, Variable v |
    use.getEnclosingFunction() = acquire.getEnclosingFunction() and
    not use.getTarget().getName().matches("%free%") and
    not use.getTarget().getName() = "kfree" and
    use.getAnArgument() = va and
    va.getTarget() = v and
    (
      exists(AssignExpr a |
        a.getRValue() = acquire and
        v = a.getLValue().(VariableAccess).getTarget()
      )
      or
      v.getInitializer().getExpr() = acquire
    )
  )
}

predicate hasNullCheckBeforeDeref(FunctionCall acquire) {
  exists(IfStmt ifStmt |
    ifStmt.getEnclosingFunction() = acquire.getEnclosingFunction() and
    (
      // Local variable via assignment: fw = kzalloc(...); if (!fw) ...
      exists(AssignExpr a, VariableAccess checkva |
        a.getRValue() = acquire and
        checkva.getTarget() = a.getLValue().(VariableAccess).getTarget() and
        ifStmt.getCondition().getAChild*() = checkva
      )
      or
      // Local variable via initializer: struct X *fw = kzalloc(...); if (!fw) ...
      exists(Variable v, VariableAccess checkva |
        v.getInitializer().getExpr() = acquire and
        checkva.getTarget() = v and
        ifStmt.getCondition().getAChild*() = checkva
      )
      or
      // Struct field: priv->pFirmware = kzalloc(...); if (!priv->pFirmware) ...
      exists(AssignExpr a, PointerFieldAccess lhs, PointerFieldAccess check |
        a.getRValue() = acquire and
        lhs = a.getLValue() and
        check.getTarget() = lhs.getTarget() and
        ifStmt.getCondition().getAChild*() = check
      )
    )
  )
}

from FunctionCall acquire
where
  isAllocCall(acquire) and
  isResultDereferenced(acquire) and
  not hasNullCheckBeforeDeref(acquire) and
  not isInFixedFunction(acquire) and
  not isInFpFunction(acquire)
select acquire,
  "Call to " + acquire.getTarget().getName() +
    " result dereferenced without NULL check, may cause NULL pointer dereference (CWE-476)"
