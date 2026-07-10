/**
 * @name  rq3-c2-err-3-rep4
 * @id    cpp/rq3/c2/err-3-rep4
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects missing error return code assignment in a function that
 *              returns an integer status variable: an error-shaped predicate
 *              (NULL/zero check) guards a goto to a cleanup label, but the
 *              status variable is not set to an error value on that path.
 */

import cpp

/** Holds if `v` is a local int-typed variable named like an error status. */
predicate isStatusVar(LocalVariable v) {
  v.getType().getUnderlyingType() instanceof IntType and
  (
    v.getName() = "ret" or
    v.getName() = "rc" or
    v.getName() = "err" or
    v.getName() = "error" or
    v.getName() = "status" or
    v.getName() = "result"
  )
}

/** Holds if `f` returns the value of `v` through at least one ReturnStmt. */
predicate functionReturnsStatusVar(Function f, LocalVariable v) {
  v.getFunction() = f and
  isStatusVar(v) and
  exists(ReturnStmt rs |
    rs.getEnclosingFunction() = f and
    rs.getExpr().(VariableAccess).getTarget() = v
  )
}

/** Holds if `v` is declared with success-value initializer 0 inside `f`. */
predicate statusVarInitializedZero(Function f, LocalVariable v) {
  functionReturnsStatusVar(f, v) and
  v.getInitializer().getExpr().getValue() = "0"
}

/** Holds if `ifs` looks like an error guard: condition is a NotExpr or an
 *  equality with zero (e.g. `!p` or `x == NULL`). */
predicate isErrorGuard(IfStmt ifs) {
  ifs.getCondition() instanceof NotExpr
  or
  exists(EqualityOperation eo |
    eo = ifs.getCondition() and
    eo.getAnOperand().getValue() = "0"
  )
}

/** Holds if `g` is a goto inside the then-branch of error-guard `ifs`. */
predicate gotoInsideErrorBranch(IfStmt ifs, GotoStmt g) {
  isErrorGuard(ifs) and
  g.getEnclosingFunction() = ifs.getEnclosingFunction() and
  g.getParent*() = ifs.getThen()
}

/** Holds if no assignment to `v` occurs lexically within the then-branch of
 *  `ifs` before the cleanup goto `g`. (Approximate: any assignment anywhere
 *  in the then-branch suffices to suppress.) */
predicate statusVarNotSetInErrorBranch(IfStmt ifs, GotoStmt g, LocalVariable v) {
  gotoInsideErrorBranch(ifs, g) and
  not exists(Assignment a |
    a.getEnclosingFunction() = ifs.getEnclosingFunction() and
    a.getParent*() = ifs.getThen() and
    a.getLValue().(VariableAccess).getTarget() = v
  )
}

from Function f, IfStmt ifs, GotoStmt g, LocalVariable v
where
  ifs.getEnclosingFunction() = f and
  g.getEnclosingFunction() = f and
  functionReturnsStatusVar(f, v) and
  statusVarInitializedZero(f, v) and
  gotoInsideErrorBranch(ifs, g) and
  statusVarNotSetInErrorBranch(ifs, g, v)
select g,
  "Missing error return code: error-guarded goto to cleanup, but status variable '" +
    v.getName() + "' is not assigned an error value on this path."
