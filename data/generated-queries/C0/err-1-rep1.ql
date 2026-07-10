/**
 * @name Missing error code assignment before goto cleanup
 * @description Detects functions that return an error variable initialized to 0,
 *              where a NULL/failure check goes to a cleanup label without first
 *              assigning a negative error code to the return variable. This is the
 *              pattern fixed by commits like 620b90d30c08 (mtd: maps: fix error
 *              return code of physmap_flash_remove).
 * @kind problem
 * @problem.severity warning
 * @id cpp/missing-error-code-before-goto
 * @tags correctness
 *       reliability
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph

/**
 * A local variable that is initialized to 0 and later returned from the function,
 * typically named `err`, `ret`, `rc`, `error`, or `status`.
 */
class ErrorReturnVar extends LocalVariable {
  ErrorReturnVar() {
    this.getType().getUnderlyingType() instanceof IntegralType and
    this.getInitializer().getExpr().getValue() = "0" and
    exists(ReturnStmt rs |
      rs.getExpr().(VariableAccess).getTarget() = this and
      rs.getEnclosingFunction() = this.getFunction()
    ) and
    this.getName().regexpMatch("(?i)err|ret|rc|error|status|result")
  }
}

/**
 * A `goto` statement whose target label is a cleanup/out label.
 */
class CleanupGoto extends GotoStmt {
  CleanupGoto() {
    this.getName().regexpMatch("(?i)out.*|err.*|fail.*|cleanup.*|done.*|exit.*|free.*|unlock.*")
  }
}

/**
 * Holds if `goto` is inside an `if` whose condition checks a pointer/value for
 * NULL/zero (failure), and the branch unconditionally goes to a cleanup label.
 */
predicate isFailureCheckGoto(IfStmt ifs, CleanupGoto gs) {
  gs.getParentStmt*() = ifs.getThen() and
  (
    // if (!x)
    ifs.getCondition() instanceof NotExpr
    or
    // if (x == NULL) or if (x < 0) or if (IS_ERR(x))
    ifs.getCondition() instanceof EqualityOperation
    or
    ifs.getCondition() instanceof RelationalOperation
    or
    exists(FunctionCall fc |
      fc = ifs.getCondition() and
      fc.getTarget().getName().regexpMatch("IS_ERR.*|.*_failed|.*_error")
    )
  )
}

/**
 * Holds if there is an assignment to `v` inside the then-branch of `ifs` before
 * `gs` executes.
 */
predicate assignsErrorBeforeGoto(IfStmt ifs, CleanupGoto gs, ErrorReturnVar v) {
  exists(AssignExpr ae |
    ae.getLValue().(VariableAccess).getTarget() = v and
    ae.getEnclosingStmt().getParentStmt*() = ifs.getThen() and
    ae.getEnclosingStmt().getLocation().getStartLine() < gs.getLocation().getStartLine()
  )
}

from Function f, ErrorReturnVar v, IfStmt ifs, CleanupGoto gs
where
  v.getFunction() = f and
  ifs.getEnclosingFunction() = f and
  gs.getEnclosingFunction() = f and
  isFailureCheckGoto(ifs, gs) and
  not assignsErrorBeforeGoto(ifs, gs, v) and
  // The cleanup label leads to (or reaches) the return that returns v.
  exists(ReturnStmt rs |
    rs.getEnclosingFunction() = f and
    rs.getExpr().(VariableAccess).getTarget() = v and
    rs.getLocation().getStartLine() > gs.getLocation().getStartLine()
  ) and
  // Exclude cases where the if-body contains an explicit return with a non-zero literal.
  not exists(ReturnStmt rs2 |
    rs2.getParentStmt*() = ifs.getThen() and
    rs2.getExpr().getValue() != "0"
  )
select gs,
  "Goto to cleanup label '" + gs.getName() +
    "' on a failure path without assigning an error code to '" + v.getName() +
    "' (initialized to 0), which will cause the function to return success."
