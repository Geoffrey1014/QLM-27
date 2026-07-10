/**
 * @name Missing error code assignment on failure path before goto cleanup
 * @description A function returns an int error code and uses a goto-cleanup pattern.
 *              On a failure path (a guard tests a result for failure, e.g. NULL or
 *              negative) the function jumps to the cleanup label without first
 *              assigning a non-zero error code to the return variable. As a result
 *              the function silently returns success (0) despite the failure.
 * @kind problem
 * @problem.severity warning
 * @id cpp/missing-error-code-before-goto
 * @tags correctness
 *       reliability
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph

/**
 * A local variable that looks like an error-code accumulator: it is an integer
 * type, is initialized to 0 (or has a 0 assignment), and is returned by the
 * enclosing function.
 */
class ErrorCodeVar extends LocalVariable {
  Function f;

  ErrorCodeVar() {
    this.getFunction() = f and
    this.getType().getUnderlyingType() instanceof IntegralType and
    // initialized to a zero constant
    exists(Expr init |
      (
        init = this.getInitializer().getExpr()
        or
        exists(AssignExpr a |
          a.getLValue() = this.getAnAccess() and
          a.getRValue() = init
        )
      ) and
      init.getValue().toInt() = 0
    ) and
    // returned by the enclosing function
    exists(ReturnStmt r |
      r.getEnclosingFunction() = f and
      r.getExpr() = this.getAnAccess()
    )
  }

  Function getEnclosingFn() { result = f }
}

/**
 * A "failure guard" if-statement whose condition is a simple failure test
 * (logical-not of a value, comparison with NULL, IS_ERR, or comparison < 0).
 */
predicate isFailureGuard(IfStmt ifs) {
  exists(Expr cond | cond = ifs.getCondition().getFullyConverted() |
    // !x
    cond instanceof NotExpr
    or
    // x == NULL / x == 0
    exists(EQExpr eq | eq = cond and eq.getAnOperand().getValue().toInt() = 0)
    or
    // x < 0
    exists(LTExpr lt |
      lt = cond and
      lt.getRightOperand().getValue().toInt() = 0
    )
    or
    // IS_ERR(x) or IS_ERR_OR_NULL(x)
    exists(FunctionCall fc |
      fc = cond and
      fc.getTarget().getName().matches("IS_ERR%")
    )
  )
}

/**
 * The then-branch body of `ifs` performs an unconditional goto to a cleanup
 * label, optionally preceded by trivial statements, but does NOT assign to
 * `errVar` before the goto.
 */
predicate gotoWithoutAssigningError(IfStmt ifs, ErrorCodeVar errVar) {
  exists(GotoStmt g |
    g.getEnclosingFunction() = errVar.getEnclosingFn() and
    g.getParent*() = ifs.getThen() and
    // no assignment to errVar inside the then-branch prior to the goto
    not exists(AssignExpr a |
      a.getLValue() = errVar.getAnAccess() and
      a.getEnclosingStmt().getParent*() = ifs.getThen()
    )
  )
}

from IfStmt ifs, ErrorCodeVar errVar, Function f
where
  f = errVar.getEnclosingFn() and
  ifs.getEnclosingFunction() = f and
  isFailureGuard(ifs) and
  gotoWithoutAssigningError(ifs, errVar) and
  // the function actually returns the variable (already enforced by ErrorCodeVar,
  // but require additionally that the return after the goto target uses errVar)
  exists(ReturnStmt r |
    r.getEnclosingFunction() = f and
    r.getExpr() = errVar.getAnAccess()
  )
select ifs,
  "Failure guard goes to cleanup without assigning an error code to '" + errVar.getName() +
    "'; function may silently return success on this failure path."
