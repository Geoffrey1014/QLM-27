/**
 * @name  rq3-c2-mc-1-rep1
 * @id    cpp/rq3/c2/mc-1-rep1
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detect unchecked return values of regmap_bulk_read (a missing-check bug).
 */

import cpp
import semmle.code.cpp.controlflow.Guards

/**
 * Recognises a call to a regmap bulk/raw read whose int return value encodes
 * a (possibly negative) errno.
 */
predicate isFallibleRegmapRead(FunctionCall fc) {
  exists(string n | n = fc.getTarget().getName() |
    n = "regmap_bulk_read" or
    n = "regmap_raw_read" or
    n = "regmap_noinc_read" or
    n = "regmap_multi_reg_read"
  )
}

/**
 * The call's return type is a (signed) integer carrying an errno convention.
 */
predicate hasErrnoReturnType(FunctionCall fc) {
  isFallibleRegmapRead(fc) and
  fc.getTarget().getType().getUnspecifiedType() instanceof IntType
}

/**
 * The call result reaches an access used as a guard condition (handles the
 * common idiom `int err = regmap_bulk_read(...); if (err) ...`).
 */
predicate resultGuarded(FunctionCall fc) {
  hasErrnoReturnType(fc) and
  (
    // The call expression is itself used to control a branch.
    exists(ControlStructure cs | cs.getControllingExpr().getAChild*() = fc)
    or
    // The call is the RHS of an initializer/assignment whose LHS is later
    // tested in a control structure or a GuardCondition.
    exists(Variable v |
      (
        exists(AssignExpr a |
          a.getRValue() = fc and a.getLValue() = v.getAnAccess()
        )
        or
        v.getInitializer().getExpr() = fc
      ) and
      (
        exists(ControlStructure cs | cs.getControllingExpr().getAChild*() = v.getAnAccess())
        or
        exists(GuardCondition g | g.(Expr).getAChild*() = v.getAnAccess())
      )
    )
    or
    // Returned directly, so the caller is responsible for checking.
    exists(ReturnStmt r | r.getExpr().getAChild*() = fc)
    or
    // Passed into an error-helper wrapper (IS_ERR / WARN / BUG family).
    exists(FunctionCall outer, string on |
      outer.getAnArgument().getAChild*() = fc and on = outer.getTarget().getName()
    |
      on.matches("IS_ERR%") or on.matches("WARN%") or on.matches("BUG%")
    )
  )
}

/**
 * The missing-check bug: an errno-returning fallible regmap read whose
 * result is dropped on the floor.
 */
predicate missingRegmapReadCheck(FunctionCall fc) {
  hasErrnoReturnType(fc) and
  not resultGuarded(fc)
}

from FunctionCall fc
where missingRegmapReadCheck(fc)
select fc,
  "Return value of " + fc.getTarget().getName() +
  " is not checked; a read failure will be silently ignored."
