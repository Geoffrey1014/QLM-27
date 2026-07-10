/**
 * @name  rq3-c2-mc-2-rep3
 * @id    cpp/rq3/c2/mc-2-rep3
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detect kzalloc allocation whose result is not null-checked
 *              before subsequent use (missing-check bug pattern).
 */

import cpp
import semmle.code.cpp.controlflow.Guards

predicate is_kzalloc_call(FunctionCall fc) {
  fc.getTarget().getName() = "kzalloc"
}

predicate kzalloc_assigned_to(FunctionCall fc, Expr lhs) {
  is_kzalloc_call(fc) and
  exists(AssignExpr ae |
    ae.getRValue() = fc and
    lhs = ae.getLValue()
  )
}

predicate expr_is_null_check_of(Expr guard, Expr target) {
  exists(EqualityOperation eq |
    eq = guard and
    eq.getAnOperand().getValue() = "0" and
    eq.getAnOperand() = target
  )
  or
  exists(NotExpr ne |
    ne = guard and
    ne.getOperand() = target
  )
}

predicate null_checked_after(FunctionCall fc, Expr lhs) {
  kzalloc_assigned_to(fc, lhs) and
  exists(Expr guard, Expr checkedTarget |
    expr_is_null_check_of(guard, checkedTarget) and
    guard.getEnclosingFunction() = fc.getEnclosingFunction() and
    checkedTarget.toString() = lhs.toString() and
    guard.getLocation().getStartLine() >= fc.getLocation().getStartLine() and
    guard.getLocation().getStartLine() <= fc.getLocation().getStartLine() + 10
  )
}

predicate missing_null_check_kzalloc(FunctionCall fc, Expr lhs) {
  kzalloc_assigned_to(fc, lhs) and
  not null_checked_after(fc, lhs)
}

from FunctionCall fc, Expr lhs
where missing_null_check_kzalloc(fc, lhs)
select fc, "kzalloc result assigned to $@ is not null-checked before use.", lhs, lhs.toString()
