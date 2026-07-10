/**
 * @name  rq3-c2-err-3-rep2
 * @id    cpp/rq3/c2/err-3-rep2
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects missing error return code assignment: a function returns
 *              a status variable through a cleanup label reached by goto from
 *              an error branch, but the status variable is never set to a
 *              non-zero error code on that branch.
 */

import cpp

/** Holds if `f` returns the value of local variable `v` at some return statement. */
predicate functionReturnsVar(Function f, LocalVariable v) {
  exists(ReturnStmt rs |
    rs.getEnclosingFunction() = f and
    rs.getExpr().(VariableAccess).getTarget() = v
  )
}

/** Holds if `v` is initialised to a success value (literal 0) at its declaration in `f`. */
predicate varInitializedToZero(Function f, LocalVariable v) {
  v.getFunction() = f and
  v.getInitializer().getExpr().getValue() = "0"
}

/** Holds if `g` is a goto inside the then-branch of an if-statement whose
 * condition is a NULL/zero check on some pointer expression (a typical error
 * branch like `if (!p) goto out;`). */
predicate isErrorBranchGoto(GotoStmt g, IfStmt ifs) {
  g.getEnclosingFunction() = ifs.getEnclosingFunction() and
  g.getParent*() = ifs.getThen() and
  (
    ifs.getCondition() instanceof NotExpr
    or
    exists(EqualityOperation eo |
      eo = ifs.getCondition() and
      eo.getAnOperand().getValue() = "0"
    )
  )
}

/** Holds if the goto target label `g` jumps to is followed (control-flow wise)
 * by a return that returns variable `v`. */
predicate gotoLeadsToReturnOfVar(GotoStmt g, LocalVariable v) {
  exists(Function f |
    g.getEnclosingFunction() = f and
    functionReturnsVar(f, v) and
    g.getTarget().getLocation().getFile() = f.getFile()
  )
}

/** Holds if variable `v` is NOT assigned anywhere inside the then-branch of
 * `ifs` (the error branch), prior to the goto `g`. */
predicate varNotAssignedInErrorBranch(IfStmt ifs, GotoStmt g, LocalVariable v) {
  isErrorBranchGoto(g, ifs) and
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
  isErrorBranchGoto(g, ifs) and
  functionReturnsVar(f, v) and
  varInitializedToZero(f, v) and
  gotoLeadsToReturnOfVar(g, v) and
  varNotAssignedInErrorBranch(ifs, g, v)
select g,
  "Possible missing error return code: goto in error branch to label that returns '" +
    v.getName() + "', but '" + v.getName() + "' is not assigned in this branch."
