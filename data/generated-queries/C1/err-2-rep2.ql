/**
 * @name Error return code missing on goto-to-cleanup path
 * @description A function returns a "status" variable through a common cleanup
 *              label reached via `goto`. On a failure-handling branch the code
 *              `goto`s the cleanup label without assigning a non-zero error
 *              code to the returned variable, so the function silently returns
 *              success (0) on the failure path.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-err-2
 */

import cpp

/** Holds if `f` returns the value of local variable `v` (possibly negated/cast). */
predicate returnsVariable(Function f, LocalVariable v) {
  exists(ReturnStmt rs |
    rs.getEnclosingFunction() = f and
    rs.getExpr() = v.getAnAccess()
  )
}

/** Holds if `ae` assigns a non-zero (error-code) expression to `v`.
 *  Heuristic: any assignment whose RHS is not the literal 0. */
predicate assignsNonZero(AssignExpr ae, LocalVariable v) {
  ae.getLValue() = v.getAnAccess() and
  not ae.getRValue().getValue() = "0"
}

/** A "failure-handling" if-statement: the condition tests a failure-like
 *  predicate (null pointer, non-positive value, error code).  We capture
 *  the common buggy idioms: `if (!x)`, `if (x == NULL)`, `if (x <= 0)`,
 *  `if (x < 0)`, `if (!y)`. */
predicate isFailureCheck(IfStmt ifs) {
  // if (!x)
  ifs.getCondition() instanceof NotExpr
  or
  // if (x <= 0) or if (x < 0) or if (x == 0)
  exists(RelationalOperation rop | rop = ifs.getCondition() |
    rop.getGreaterOperand().getValue() = "0"
  )
  or
  exists(EQExpr eq | eq = ifs.getCondition() |
    eq.getAnOperand().getValue() = "0"
  )
}

from Function f, LocalVariable retVar, IfStmt failCheck, GotoStmt gs, Stmt thenStmt
where
  // f returns retVar
  returnsVariable(f, retVar) and
  retVar.getFunction() = f and
  retVar.getType().getUnspecifiedType() instanceof IntegralType and
  // the failing if-stmt is inside f
  failCheck.getEnclosingFunction() = f and
  isFailureCheck(failCheck) and
  // its then-branch contains a goto to a cleanup label
  thenStmt = failCheck.getThen() and
  gs.getParent*() = thenStmt and
  // no assignment of a non-zero value to retVar on this branch (then-stmt)
  not exists(AssignExpr ae |
    assignsNonZero(ae, retVar) and
    ae.getEnclosingStmt().getParent*() = thenStmt
  ) and
  // and no direct return-with-error in the same branch
  not exists(ReturnStmt rs |
    rs.getParent*() = thenStmt and
    not rs.getExpr() = retVar.getAnAccess()
  ) and
  // exclude trivial cases: goto must lead (transitively) to a return of retVar
  // (i.e., this really is the cleanup label that returns the status).
  exists(ReturnStmt rs |
    rs.getEnclosingFunction() = f and
    rs.getExpr() = retVar.getAnAccess() and
    gs.getTarget().getASuccessor*() = rs
  ) and
  // the if-condition must NOT itself read retVar (if it does, retVar already
  // holds the error code -- e.g. `if (ret < 0) goto free;`).
  not exists(VariableAccess va |
    va = retVar.getAnAccess() and
    va.getParent*() = failCheck.getCondition()
  ) and
  // and no assignment of a non-zero value to retVar between the goto target
  // and the return that would set the error code in the cleanup landing pad.
  not exists(AssignExpr ae, ReturnStmt rs2 |
    assignsNonZero(ae, retVar) and
    ae.getEnclosingFunction() = f and
    gs.getTarget().getASuccessor*() = ae and
    rs2.getExpr() = retVar.getAnAccess() and
    ae.getASuccessor*() = rs2
  )
select gs,
  "Missing error-code assignment to '" + retVar.getName() +
    "' before goto to cleanup; function may return success on this failure path."
