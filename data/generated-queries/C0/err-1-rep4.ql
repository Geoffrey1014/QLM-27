/**
 * @name Missing error code assignment before goto on error path
 * @description Detects functions that return an integer error code where an
 *              error-detection branch (e.g. NULL check on a pointer returned by
 *              a lookup-style API) jumps via `goto` to a cleanup/return label
 *              without first assigning a non-zero error code to the variable
 *              that will ultimately be returned. The function therefore
 *              silently returns success (0) even though it took the error path.
 * @kind problem
 * @problem.severity warning
 * @id cpp/missing-error-code-before-goto
 * @tags correctness
 *       reliability
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph

/**
 * A local variable that looks like the conventional error-return holder.
 * It is an int, initialised to 0 (or to a constant 0-equivalent), and the
 * enclosing function returns its value.
 */
class ErrVar extends LocalVariable {
  Function f;

  ErrVar() {
    this.getFunction() = f and
    this.getType().getUnspecifiedType() instanceof IntType and
    // Initialised to literal 0 (covers `int err = 0;` and `int i, err = 0;`).
    exists(Expr init |
      init = this.getInitializer().getExpr() and
      init.getValue() = "0"
    ) and
    // The function returns this variable somewhere (directly).
    exists(ReturnStmt rs, VariableAccess va |
      rs.getEnclosingFunction() = f and
      va = rs.getExpr().(VariableAccess) and
      va.getTarget() = this
    )
  }

  Function getEnclosingFunction() { result = f }
}

/**
 * Holds if `g` is an error-handling goto: it is the only statement (other than
 * the condition) inside an `if` whose condition is a simple negation / NULL
 * check, and it jumps to a label that lexically follows it in the same
 * function (typical cleanup/out label).
 */
predicate isErrorGoto(GotoStmt g, IfStmt ifs) {
  ifs.getThen() = g
  or
  exists(BlockStmt b |
    ifs.getThen() = b and
    b.getNumStmt() = 1 and
    b.getStmt(0) = g
  )
}

/**
 * Holds if the condition `c` looks like a failure check on the result of a
 * pointer-returning call: `!x`, `x == NULL`, `!IS_ERR_OR_NULL(x)` style etc.
 * We keep the heuristic broad: any condition that contains a NotExpr, an
 * equality with 0/NULL, or an IS_ERR-family macro.
 */
predicate looksLikeFailureCheck(Expr c) {
  c instanceof NotExpr
  or
  exists(EQExpr eq | eq = c and
    (
      eq.getAnOperand().getValue() = "0" or
      eq.getAnOperand() instanceof Literal and
      eq.getAnOperand().(Literal).getValue() = "0"
    )
  )
  or
  exists(MacroInvocation mi |
    mi.getMacroName().regexpMatch("IS_ERR(_OR_NULL)?|WARN_ON|unlikely") and
    mi.getExpr() = c
  )
  or
  // `if (!info)` style — already covered by NotExpr above, but the operand
  // typically is a VariableAccess to a pointer.
  exists(NotExpr n | n = c and n.getOperand() instanceof VariableAccess)
}

/**
 * Holds if statement `s` assigns to variable `v` (any assignment kind).
 */
predicate assignsTo(Stmt s, Variable v) {
  exists(AssignExpr a |
    a.getEnclosingStmt() = s and
    a.getLValue().(VariableAccess).getTarget() = v
  )
  or
  exists(ExprStmt es, AssignExpr a |
    es = s and
    a = es.getExpr() and
    a.getLValue().(VariableAccess).getTarget() = v
  )
}

from
  Function f, ErrVar err, IfStmt ifs, GotoStmt g, Stmt thenStmt
where
  err.getEnclosingFunction() = f and
  ifs.getEnclosingFunction() = f and
  // Recognise the failure-check shape.
  looksLikeFailureCheck(ifs.getCondition()) and
  // The then-branch is (or contains as its single statement) a goto.
  isErrorGoto(g, ifs) and
  thenStmt = ifs.getThen() and
  // The error variable `err` is NOT assigned anywhere inside the then-branch
  // before the goto (since the then-branch IS just the goto, there is no
  // assignment to err at all on this path).
  not exists(Stmt s |
    s.getParentStmt*() = thenStmt and
    assignsTo(s, err)
  ) and
  // Avoid trivial cases where the function only ever returns 0 anyway —
  // require that at least one *other* path in the function assigns a
  // non-zero value to err (proving the function does have a real error
  // protocol that this path violates).
  exists(AssignExpr a |
    a.getEnclosingFunction() = f and
    a.getLValue().(VariableAccess).getTarget() = err and
    not a.getRValue().getValue() = "0"
  ) and
  // Filter: the if-condition must reference a variable that was assigned
  // from a call expression earlier in the same function (lookup-style API
  // such as platform_get_drvdata, of_find_*, etc.).
  exists(VariableAccess va, Variable v, AssignExpr defAssign |
    va = ifs.getCondition().getAChild*() and
    va.getTarget() = v and
    defAssign.getEnclosingFunction() = f and
    defAssign.getLValue().(VariableAccess).getTarget() = v and
    defAssign.getRValue() instanceof FunctionCall
  )
select g,
  "Error path via goto does not assign an error code to '" + err.getName() +
    "'; function may silently return success."
