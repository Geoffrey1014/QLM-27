/**
 * @name Missing check of return value from SMBus/regmap-style read function
 * @description Detects call sites where a *_read_value / *_read integer-returning
 *              helper's result is used directly without checking for a negative
 *              errno. Pattern origin: c9c63915519b hwmon (lm80) fix.
 * @kind problem
 * @problem.severity warning
 * @id qlm/missing-check-smbus-read
 * @tags reliability
 *       correctness
 *       cwe-252
 */
import cpp

/* Broad predicate: the fc-target is an int-returning read helper whose
 * result is used somewhere in the enclosing function without an if-based
 * check of the value returned by the same call (either directly or via a
 * local variable that holds it). */
predicate isMissingCheckOfRead(FunctionCall fc) {
  exists(Function f | f = fc.getTarget() |
    f.getName() = "lm80_read_value" or
    f.getName().matches("%\\_read\\_value") or
    f.getName().matches("regmap%read") or
    f.getName().matches("smbus\\_read%") or
    f.getName().matches("i2c%read%")
  ) and
  fc.getType().getUnspecifiedType() instanceof IntType and
  // used non-trivially (avoid pure `(void)fc()` discard forms)
  exists(Expr use |
    use.getParent*() = fc.getEnclosingStmt() and
    (use instanceof BitwiseAndExpr or use instanceof BitwiseOrExpr or
     use instanceof AssignExpr or use instanceof VariableAccess or
     use = fc)
  ) and
  // no direct check of the call in this function
  not exists(IfStmt ic |
    ic.getEnclosingFunction() = fc.getEnclosingFunction() and
    ic.getCondition().getAChild*() = fc
  ) and
  // no indirect check via a local variable holding the call result
  not exists(LocalVariable v, IfStmt ic2 |
    v.getInitializer().getExpr() = fc and
    ic2.getEnclosingFunction() = fc.getEnclosingFunction() and
    ic2.getCondition().getAChild*().(VariableAccess).getTarget() = v
  ) and
  not exists(LocalVariable v2, AssignExpr ae, IfStmt ic3 |
    ae.getLValue().(VariableAccess).getTarget() = v2 and
    ae.getRValue() = fc and
    ic3.getEnclosingFunction() = fc.getEnclosingFunction() and
    ic3.getCondition().getAChild*().(VariableAccess).getTarget() = v2
  )
}

from FunctionCall fc
where isMissingCheckOfRead(fc)
select fc,
  "Missing check of return value from " + fc.getTarget().getName() +
  " (may return negative errno on I2C/SMBus failure)"
