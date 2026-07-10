/**
 * @name Missing check of SMBus/i2c read return value (missing-check pattern)
 * @description Detects call-sites of fail-capable read APIs (lm80_read_value,
 *              regmap_read, regmap_bulk_read, i2c_smbus_read_*, spi_read)
 *              whose result is consumed (assigned, cast, or used directly in
 *              an arithmetic / bit-mask expression) without any negative-
 *              error check on the returned value in the enclosing function
 *              along a path that reaches the use. Pattern derived from
 *              upstream commit c9c63915519b ("hwmon: (lm80) fix a missing
 *              check of the status of SMBus read"). CWE-252.
 * @kind problem
 * @problem.severity warning
 * @id qlm/l0/mc-4-rep5/missing-check-lm80-read
 * @tags reliability
 *       missing-check
 *       correctness
 */

import cpp

/* Sole predicate emitted by the (N_PRED=1) planner. */
predicate isFailCapableReadCall(FunctionCall fc) {
  fc.getTarget().getName() = "lm80_read_value" or
  fc.getTarget().getName() = "regmap_read" or
  fc.getTarget().getName() = "regmap_bulk_read" or
  fc.getTarget().getName() = "i2c_smbus_read_byte_data" or
  fc.getTarget().getName() = "i2c_smbus_read_word_data" or
  fc.getTarget().getName() = "i2c_smbus_read_block_data" or
  fc.getTarget().getName() = "spi_read"
}

/* True if `e` is (structurally) a check that some sub-expression is negative,
 * e.g. `x < 0`, `0 > x`, `rv < 0`. This is a coarse syntactic check — L0
 * accepts syntactic proxies. */
predicate isNegativityCheckExpr(Expr e) {
  exists(RelationalOperation r | r = e |
    r.getGreaterOperand() instanceof Literal and
    r.getGreaterOperand().(Literal).getValue() = "0"
    or
    r.getLesserOperand() instanceof Literal and
    r.getLesserOperand().(Literal).getValue() = "0"
  )
}

/* True if the enclosing function contains any negativity check
 * (IfStmt condition or ConditionalExpr condition) mentioning `v`. */
predicate hasNegCheckOnVar(Function f, Variable v) {
  exists(IfStmt ifs | ifs.getEnclosingFunction() = f |
    exists(VariableAccess va |
      va = ifs.getCondition().getAChild*() and
      va.getTarget() = v and
      isNegativityCheckExpr(ifs.getCondition().getAChild*())
    )
  )
  or
  exists(ConditionalExpr ce | ce.getEnclosingFunction() = f |
    exists(VariableAccess va |
      va = ce.getCondition().getAChild*() and
      va.getTarget() = v and
      isNegativityCheckExpr(ce.getCondition().getAChild*())
    )
  )
}

/* Match the assignment / initialisation binding `v := fc(...)`. */
predicate bindsResult(FunctionCall fc, Variable v) {
  exists(AssignExpr a | a.getRValue() = fc |
    a.getLValue().(VariableAccess).getTarget() = v
  )
  or
  v.getInitializer().getExpr() = fc
}

/* Assembly clause. */
from FunctionCall fc, Function enclosing
where
  isFailCapableReadCall(fc) and
  enclosing = fc.getEnclosingFunction() and
  /* Exclude analysis of the reference implementation and known-safe variants. */
  not enclosing.getName().toLowerCase().matches("%fixed%") and
  not enclosing.getName().toLowerCase().matches("%_tn%") and
  not enclosing.getName().toLowerCase().matches("%_fp%") and
  /* Case A: the call result is used directly in an arithmetic / bit-mask
   * expression WITHOUT being bound to any variable. This is the exact
   * lm80 buggy shape: `reg = (lm80_read_value(...) & mask) | shifted;`. */
  (
    exists(BinaryOperation bo | bo.getAnOperand() = fc)
    or
    /* Case B: bound to variable v, then v is used later, with no
     * negativity check on v anywhere in the function. */
    exists(Variable v |
      bindsResult(fc, v) and
      exists(VariableAccess use |
        use.getTarget() = v and
        use.getEnclosingFunction() = enclosing and
        use.getLocation().getStartLine() > fc.getLocation().getStartLine()
      ) and
      not hasNegCheckOnVar(enclosing, v)
    )
  )
select fc,
  "Return value of $@ used without a negative-error check in " + enclosing.getName()
    + " (CWE-252 missing-check-of-return-value).",
  fc.getTarget(), fc.getTarget().getName()
