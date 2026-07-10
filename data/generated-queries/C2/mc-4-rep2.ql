/**
 * @name  rq3-c2-mc-4-rep2
 * @id    cpp/rq3/c2/mc-4-rep2
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects calls to lm80_read_value (or similar SMBus read helpers)
 *              whose return value is used without an error check.
 */
import cpp

predicate isTargetCall(FunctionCall fc) {
  fc.getTarget().getName() = "lm80_read_value"
}

predicate resultStoredIn(FunctionCall fc, Variable v) {
  isTargetCall(fc) and
  (
    exists(AssignExpr ae | ae.getRValue() = fc and ae.getLValue() = v.getAnAccess())
    or
    exists(Initializer init | init.getExpr() = fc and init.getDeclaration() = v)
  )
}

predicate isErrorCheckedBeforeUse(FunctionCall fc, Variable v) {
  resultStoredIn(fc, v) and
  exists(IfStmt ifs, RelationalOperation cmp |
    ifs.getCondition().getAChild*() = cmp and
    cmp.getAnOperand() = v.getAnAccess() and
    cmp.getAnOperand().getValue().toInt() = 0
  )
}

predicate usedWithoutCheck(FunctionCall fc) {
  isTargetCall(fc) and
  (
    // direct use: not stored, used inline as part of a larger expression
    not exists(Variable v | resultStoredIn(fc, v)) and
    fc.getParent() instanceof Expr
    or
    // stored but never error-checked
    exists(Variable v | resultStoredIn(fc, v) and not isErrorCheckedBeforeUse(fc, v))
  )
}

predicate missingErrorCheck(FunctionCall fc) {
  usedWithoutCheck(fc)
}

from FunctionCall fc
where missingErrorCheck(fc)
select fc, "Return value of lm80_read_value used without checking for error (negative value)."
