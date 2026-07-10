/**
 * @name  rq3-c2-mc-4-rep3
 * @id    cpp/rq3/c2/mc-4-rep3
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects missing checks of SMBus / register read return values
 *              that may be negative errnos but are consumed as data.
 */
import cpp

predicate isFallibleSmbusCall(FunctionCall fc) {
  exists(Function f | f = fc.getTarget() |
    f.getName() = "lm80_read_value" or
    f.getName().matches("%_read_value") or
    f.getName().matches("i2c_smbus_read%") or
    f.getName().matches("smbus_read%")
  ) and
  fc.getType().getUnderlyingType() instanceof IntegralType
}

predicate usedAsData(FunctionCall fc) {
  isFallibleSmbusCall(fc) and
  (
    exists(BinaryOperation bop |
      bop.getAnOperand() = fc and
      (bop instanceof BitwiseAndExpr or bop instanceof BitwiseOrExpr or
       bop instanceof BitwiseXorExpr or bop instanceof LShiftExpr or
       bop instanceof RShiftExpr or bop instanceof AddExpr or
       bop instanceof SubExpr or bop instanceof MulExpr or
       bop instanceof DivExpr)
    )
    or
    exists(Assignment a | a.getRValue() = fc)
    or
    exists(ArrayExpr ae | ae.getArrayOffset() = fc)
  )
}

predicate isCheckedNegative(FunctionCall fc) {
  isFallibleSmbusCall(fc) and
  (
    exists(ComparisonOperation cmp |
      cmp.getAnOperand() = fc and
      cmp.getAnOperand().getValue().toInt() = 0
    )
    or
    exists(Variable v, Assignment a, ComparisonOperation cmp |
      a.getRValue() = fc and
      a.getLValue() = v.getAnAccess() and
      cmp.getAnOperand() = v.getAnAccess() and
      cmp.getAnOperand().getValue().toInt() = 0
    )
    or
    exists(MacroInvocation mi |
      mi.getMacroName().matches("IS_ERR%") and
      mi.getExpr().getAChild*() = fc
    )
  )
}

predicate missingNegCheck(FunctionCall fc) {
  usedAsData(fc) and
  not isCheckedNegative(fc)
}

from FunctionCall fc
where missingNegCheck(fc)
select fc,
  "Return value of fallible SMBus/register read '" + fc.getTarget().getName() +
  "' is used as data without checking for negative errno."
