/**
 * @name Missing error code assignment before goto cleanup
 * @description Detects functions where an error condition (failed allocation,
 *              lookup, etc.) jumps to a cleanup label via goto without first
 *              assigning a negative error code to the return variable. When the
 *              cleanup path returns the (possibly zero) return variable, the
 *              caller sees success despite the error.
 * @kind problem
 * @problem.severity warning
 * @id cpp/missing-error-code-before-goto
 * @tags reliability
 *       correctness
 */

import cpp
import semmle.code.cpp.controlflow.ControlFlowGraph

/**
 * Holds if `f` returns `int` (a common kernel error-code convention).
 */
predicate returnsInt(Function f) {
  f.getType().getUnspecifiedType() instanceof IntType
}

/**
 * The "return variable" of `f`: a local int variable that is returned at some
 * point via `return ret;`.
 */
class ReturnVar extends LocalVariable {
  Function func;

  ReturnVar() {
    this.getFunction() = func and
    returnsInt(func) and
    this.getType().getUnspecifiedType() instanceof IntType and
    exists(ReturnStmt rs, VariableAccess va |
      rs.getEnclosingFunction() = func and
      va = rs.getExpr() and
      va.getTarget() = this
    )
  }

  Function getEnclosingFunc() { result = func }
}

/**
 * Holds if `init` is the (only) initializer / dominant initial assignment of
 * `v` and assigns the literal 0 (or no initializer at all, defaulting to 0
 * conceptually).  We use this to detect when the return variable starts at 0.
 */
predicate initialisedToZero(ReturnVar v) {
  // Declared with initializer = 0
  exists(Expr init | init = v.getInitializer().getExpr() |
    init.getValue().toInt() = 0
  )
  or
  // Declared without initializer, but later explicitly assigned 0 as the first
  // assignment near the top of the function (common kernel idiom: int ret = 0;).
  not exists(v.getInitializer())
}

/**
 * A condition check that looks like an error detection: tests whether a
 * pointer/result is NULL or negative.
 */
class ErrorCheck extends IfStmt {
  ErrorCheck() {
    // if (!x)  or  if (x == NULL)  or  if (IS_ERR(x))  or  if (x < 0)
    exists(Expr cond | cond = this.getCondition() |
      cond instanceof NotExpr
      or
      exists(EQExpr eq | eq = cond and eq.getAnOperand().getValue() = "0")
      or
      exists(LTExpr lt |
        lt = cond and lt.getRightOperand().getValue().toInt() = 0
      )
      or
      exists(FunctionCall fc |
        fc = cond.(FunctionCall) and
        fc.getTarget().getName().regexpMatch("IS_ERR(_OR_NULL)?")
      )
    )
  }
}

/**
 * Holds if the statement (or one of its descendants) is a `goto`.
 */
predicate containsGoto(Stmt s, GotoStmt g) {
  g = s
  or
  g.getParent+() = s
}

/**
 * Holds if statement `s` (or any nested statement) assigns to `v`.
 */
predicate assignsTo(Stmt s, LocalVariable v) {
  exists(AssignExpr a |
    a.getEnclosingStmt() = s or a.getEnclosingStmt().getParent+() = s
  |
    a.getLValue().(VariableAccess).getTarget() = v
  )
}

from
  Function f, ReturnVar ret, ErrorCheck ec, GotoStmt g, Stmt thenStmt
where
  f = ret.getEnclosingFunc() and
  ec.getEnclosingFunction() = f and
  initialisedToZero(ret) and
  thenStmt = ec.getThen() and
  containsGoto(thenStmt, g) and
  // The goto target label has at least one other predecessor reachable on the
  // success path (i.e. it's a shared cleanup label, not an error-only label).
  exists(GotoStmt other |
    other.getTarget() = g.getTarget() and
    other != g and
    other.getEnclosingFunction() = f
  ) and
  // After the cleanup label, control reaches `return ret;`.
  exists(ReturnStmt rs |
    rs.getEnclosingFunction() = f and
    rs.getExpr().(VariableAccess).getTarget() = ret
  ) and
  // The error branch does NOT assign ret before the goto.
  not assignsTo(thenStmt, ret) and
  // Exclude trivial cases where the condition itself is checking ret.
  not ec.getCondition().(VariableAccess).getTarget() = ret
select g,
  "Error branch jumps to shared cleanup label '" + g.getName() +
    "' without assigning an error code to return variable '" + ret.getName() +
    "'; function may return 0 (success) on this error path."
