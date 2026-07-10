/**
 * @name Missing error return code before goto cleanup
 * @description A function declares a return-code variable (e.g. `ret`) that is
 *              returned at the cleanup label, but a failure-handling branch
 *              jumps to that cleanup label via `goto` without assigning a
 *              non-zero / negative error code to the variable first. The
 *              function therefore returns success (0) on a real failure.
 * @kind problem
 * @problem.severity warning
 * @id cpp/missing-error-return-before-goto
 * @tags correctness
 *       reliability
 */

import cpp
import semmle.code.cpp.controlflow.Guards

/**
 * A local variable that looks like an error-return holder: integer typed,
 * named like `ret`/`err`/`rc`/`error`/`status`, and actually used as the
 * operand of a `return` statement inside its enclosing function.
 */
class RetVar extends LocalVariable {
  RetVar() {
    this.getType().getUnspecifiedType() instanceof IntegralType and
    this.getName().regexpMatch("(?i)^(ret|rc|err|error|status|rv|r)$") and
    exists(ReturnStmt rs, Function f |
      f = this.getFunction() and
      rs.getEnclosingFunction() = f and
      rs.getExpr().(VariableAccess).getTarget() = this
    )
  }
}

/**
 * Holds if `rv` has any reaching definition that assigns a clearly negative
 * (error) value somewhere in `f`. This is used to confirm the function does
 * use `rv` as an error code in normal flow.
 */
predicate hasErrorAssignment(RetVar rv, Function f) {
  rv.getFunction() = f and
  exists(Assignment a |
    a.getEnclosingFunction() = f and
    a.getLValue().(VariableAccess).getTarget() = rv and
    (
      a.getRValue().getValue().toInt() < 0
      or
      // -E<NAME> macros expand to negative integers, but also catch common spellings
      a.getRValue().(UnaryMinusExpr).getOperand() instanceof Expr
      or
      a.getRValue().toString().regexpMatch("-E[A-Z]+")
    )
  )
}

/**
 * A `goto` statement that jumps to a label whose post-label code path leads to
 * `return rv;`, where `rv` is the return-code variable of the enclosing
 * function.
 */
class CleanupGoto extends GotoStmt {
  RetVar rv;

  CleanupGoto() {
    exists(Function f, ReturnStmt rs |
      f = this.getEnclosingFunction() and
      rv.getFunction() = f and
      rs.getEnclosingFunction() = f and
      rs.getExpr().(VariableAccess).getTarget() = rv and
      // The goto's target label is reachable to the return (any cleanup label
      // returning rv counts).
      this.getTarget().getLocation().getFile() = rs.getLocation().getFile()
    )
  }

  RetVar getRetVar() { result = rv }
}

/**
 * Holds if `g` is dominated by a guard whose condition indicates a failure
 * (e.g. `!ptr`, `ptr == NULL`, `count <= 0`, `count == 0`, `ret < 0`) — i.e.
 * the goto is plainly on a failure path.
 */
predicate gotoOnFailurePath(CleanupGoto g) {
  exists(IfStmt ifs |
    ifs.getEnclosingFunction() = g.getEnclosingFunction() and
    (
      ifs.getThen() = g or
      ifs.getThen().(BlockStmt).getAStmt() = g or
      ifs.getElse() = g or
      ifs.getElse().(BlockStmt).getAStmt() = g
    ) and
    (
      // !x   /  x == NULL  / x == 0
      ifs.getCondition() instanceof NotExpr or
      exists(EQExpr eq | eq = ifs.getCondition() and eq.getAnOperand().getValue() = "0") or
      // x <= 0  /  x < 0
      exists(LEExpr le | le = ifs.getCondition() and le.getRightOperand().getValue() = "0") or
      exists(LTExpr lt | lt = ifs.getCondition() and lt.getRightOperand().getValue() = "0") or
      // IS_ERR / IS_ERR_OR_NULL style
      exists(FunctionCall fc |
        fc = ifs.getCondition() and
        fc.getTarget().getName().regexpMatch("IS_ERR.*")
      )
    )
  )
}

/**
 * Holds if between the failure-detecting guard and the `goto`, `rv` has been
 * assigned an error code. We approximate this by checking whether the goto's
 * basic-block (or the if-then block containing it) has an assignment to `rv`
 * that precedes the goto textually inside the same compound statement.
 */
predicate assignsRetBeforeGoto(CleanupGoto g) {
  exists(Assignment a |
    a.getEnclosingFunction() = g.getEnclosingFunction() and
    a.getLValue().(VariableAccess).getTarget() = g.getRetVar() and
    a.getLocation().getStartLine() <= g.getLocation().getStartLine() and
    a.getLocation().getStartLine() >=
      g.getLocation().getStartLine() - 5
  )
}

from CleanupGoto g, RetVar rv, Function f
where
  rv = g.getRetVar() and
  f = g.getEnclosingFunction() and
  hasErrorAssignment(rv, f) and
  gotoOnFailurePath(g) and
  not assignsRetBeforeGoto(g) and
  // Exclude the trivial case where the very first reaching def of rv at the
  // start of the function is already negative (then "0" is impossible — but
  // that almost never happens for these patterns).
  not exists(Initializer init |
    init = rv.getInitializer() and
    init.getExpr().getValue().toInt() < 0
  )
select g,
  "Goto to cleanup on a failure path without assigning an error code to '" +
    rv.getName() + "'; function may return success (0) on failure."
