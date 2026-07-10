/**
 * @name Missing error code assignment before goto cleanup
 * @description A function declares a local error variable initialized to a
 *              success value (0), then takes an early goto to a cleanup label
 *              on a failure condition (e.g. NULL pointer check) without
 *              assigning a non-zero error code. The function consequently
 *              returns success even though an error occurred.
 * @kind problem
 * @problem.severity warning
 * @id cpp/missing-error-code-before-goto
 * @tags correctness
 *       reliability
 */

import cpp
import semmle.code.cpp.controlflow.Guards

/**
 * A local variable that looks like an error/return code:
 *  - integer-typed
 *  - named like `err`, `ret`, `rc`, `error`, `status`
 *  - initialized to 0 (success) at declaration
 */
class ErrVar extends LocalVariable {
  ErrVar() {
    this.getType().getUnspecifiedType() instanceof IntegralType and
    this.getName().regexpMatch("(?i)(err|ret|rc|error|status|result)") and
    exists(Expr init | init = this.getInitializer().getExpr() |
      init.getValue().toInt() = 0
    )
  }
}

/**
 * A goto statement that targets a label whose name looks like a cleanup
 * label (`out`, `err`, `fail`, `cleanup`, `unlock`, `done`).
 */
class CleanupGoto extends GotoStmt {
  CleanupGoto() {
    this.getName().regexpMatch("(?i)(out|err|fail|cleanup|unlock|done|exit)(_.*)?")
  }
}

/**
 * Holds if `g` is a goto inside the `then` (or `else`) branch of an `if`
 * whose condition is a null/failure check (e.g. `if (!p) goto out;` or
 * `if (p == NULL) goto out;` or `if (IS_ERR(p)) goto out;`).
 */
predicate isFailureBranchGoto(CleanupGoto g, IfStmt ifs) {
  ifs.getThen() = g
  or
  exists(BlockStmt b | ifs.getThen() = b and b.getAStmt() = g and b.getNumStmt() = 1)
}

/**
 * Holds if the condition of `ifs` looks like a "something went wrong" check:
 *  - `!x`
 *  - `x == 0` / `x == NULL`
 *  - `IS_ERR(x)` / `IS_ERR_OR_NULL(x)`
 */
predicate isFailureCondition(IfStmt ifs) {
  exists(NotExpr n | n = ifs.getCondition())
  or
  exists(EQExpr eq | eq = ifs.getCondition() |
    eq.getAnOperand().getValue().toInt() = 0
  )
  or
  exists(FunctionCall fc | fc = ifs.getCondition() |
    fc.getTarget().getName().regexpMatch("IS_ERR(_OR_NULL)?")
  )
  or
  exists(FunctionCall fc, NotExpr n |
    n = ifs.getCondition() and fc = n.getOperand() and
    fc.getTarget().getName().regexpMatch("IS_ERR(_OR_NULL)?")
  )
}

/**
 * Holds if any statement in the `then` branch of `ifs` assigns to `v`.
 */
predicate assignsInThen(IfStmt ifs, ErrVar v) {
  exists(AssignExpr a |
    a.getEnclosingStmt().getParentStmt*() = ifs.getThen() and
    a.getLValue() = v.getAnAccess()
  )
}

/**
 * The cleanup label `out:` doesn't itself re-assign `v` between the label
 * and the eventual `return v;`. We approximate: the function's return
 * statement returns `v`, meaning whatever value `v` holds at the goto is
 * what gets returned.
 */
predicate returnsErrVar(Function f, ErrVar v) {
  exists(ReturnStmt rs | rs.getEnclosingFunction() = f |
    rs.getExpr() = v.getAnAccess()
  )
}

from Function f, ErrVar v, CleanupGoto g, IfStmt ifs
where
  v.getFunction() = f and
  g.getEnclosingFunction() = f and
  isFailureBranchGoto(g, ifs) and
  ifs.getEnclosingFunction() = f and
  isFailureCondition(ifs) and
  not assignsInThen(ifs, v) and
  returnsErrVar(f, v) and
  // the goto must occur *before* any assignment to v that would set a real
  // error code at this same program point — i.e. the if-branch contains no
  // assignment to v at all.
  not exists(AssignExpr a |
    a.getLValue() = v.getAnAccess() and
    a.getEnclosingStmt().getParentStmt*() = ifs.getThen()
  )
select g,
  "Goto to cleanup label '" + g.getName() +
    "' on failure branch without assigning error code to '" + v.getName() +
    "'; function will return success (0)."
