/**
 * @name  rq3-c2-mc-4-rep1
 * @id    cpp/rq3/c2/mc-4-rep1
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2 (missing-check pattern).
 */
import cpp
import semmle.code.cpp.controlflow.Guards

/**
 * A call whose target returns a signed integer that can encode an error
 * (e.g. negative errno from an SMBus/i2c read helper).
 */
predicate is_fallible_call(FunctionCall fc) {
  exists(Function f | f = fc.getTarget() |
    f.getType().getUnspecifiedType() instanceof IntType and
    (
      f.getName().matches("%read%") or
      f.getName().matches("%get%") or
      f.getName().matches("%recv%") or
      f.getName().matches("%fetch%")
    ) and
    not f.getName().matches("%readable%")
  )
}

/**
 * The return value of `fc` flows directly into a use that treats it as
 * data — e.g. bitwise/arithmetic ops, an array index, or an assignment
 * to a narrower integer type — without first being checked.
 */
predicate return_used_as_data(FunctionCall fc) {
  is_fallible_call(fc) and
  (
    exists(BitwiseAndExpr b | b.getAnOperand() = fc) or
    exists(BitwiseOrExpr b | b.getAnOperand() = fc) or
    exists(RShiftExpr b | b.getAnOperand() = fc) or
    exists(LShiftExpr b | b.getAnOperand() = fc) or
    exists(ArrayExpr a | a.getArrayOffset() = fc) or
    exists(Assignment a, Variable v |
      a.getRValue() = fc and
      a.getLValue() = v.getAnAccess() and
      v.getType().getSize() < fc.getTarget().getType().getSize()
    )
  )
}

/**
 * The return value of `fc` is checked for an error condition (compared
 * against 0 / negative, or fed into IS_ERR-like macros) in the same
 * function as `fc`.
 */
predicate return_checked_for_error(FunctionCall fc) {
  exists(Variable v, AssignExpr a |
    a.getRValue() = fc and
    a.getLValue() = v.getAnAccess() and
    exists(ComparisonOperation cmp, VariableAccess va |
      va = v.getAnAccess() and
      cmp.getAnOperand() = va and
      cmp.getEnclosingFunction() = fc.getEnclosingFunction()
    )
  )
  or
  exists(ComparisonOperation cmp | cmp.getAnOperand() = fc)
  or
  exists(FunctionCall errCheck |
    errCheck.getTarget().getName().matches("IS\\_ERR%") and
    errCheck.getAnArgument() = fc
  )
}

/**
 * A fallible call whose return value is used as data, in a function
 * context where no error check is performed on it.
 */
predicate missing_check_bug(FunctionCall fc) {
  is_fallible_call(fc) and
  return_used_as_data(fc) and
  not return_checked_for_error(fc)
}

from FunctionCall fc
where missing_check_bug(fc)
select fc,
  "Return value of fallible call '" + fc.getTarget().getName() +
  "' used as data without a negative-error check."
