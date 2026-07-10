/**
 * @name Missing error return code before cleanup goto
 * @description An error is detected and logged (e.g. via dev_err/pr_err) and the
 *              code branches via `goto <label>` to a cleanup/exit block that returns
 *              `ret`, but `ret` is not assigned a negative errno on this path. The
 *              function therefore returns 0 (or a stale, possibly success value)
 *              even though an error was reported. This mirrors commit
 *              26594c6bbb60 ("rpmsg: qcom_glink_native: fix error return code of
 *              qcom_glink_rx_data()").
 * @kind problem
 * @problem.severity warning
 * @id cpp/missing-error-return-code-before-goto
 * @tags correctness
 *       reliability
 */

import cpp

/** A function whose return type is a signed integer (typical kernel errno-returning). */
class IntReturningFunction extends Function {
  IntReturningFunction() {
    this.getType().getUnspecifiedType() instanceof IntType
  }
}

/** A kernel-style error-logging call. */
class ErrorLogCall extends FunctionCall {
  ErrorLogCall() {
    exists(string n | n = this.getTarget().getName() |
      n = "dev_err" or
      n = "dev_err_ratelimited" or
      n = "dev_err_probe" or
      n = "pr_err" or
      n = "pr_err_ratelimited" or
      n = "netdev_err" or
      n = "WARN" or
      n = "WARN_ON" or
      n = "WARN_ONCE"
    )
  }
}

/**
 * A local `int`-typed variable named "ret"/"err"/"rc"/"error" — the canonical
 * kernel error accumulator.
 */
class ErrorVar extends LocalVariable {
  ErrorVar() {
    this.getType().getUnspecifiedType() instanceof IntType and
    (
      this.getName() = "ret" or
      this.getName() = "err" or
      this.getName() = "rc" or
      this.getName() = "error" or
      this.getName() = "status"
    )
  }
}

/** A `goto Label;` statement. */
class GotoLabel extends GotoStmt { }

/**
 * Holds if statement `s` assigns to `v` (direct assignment or via address-of in
 * a sibling call is NOT counted — we want plain `v = expr`).
 */
predicate assignsErrorVar(Stmt s, ErrorVar v) {
  exists(Assignment a |
    a.getLValue() = v.getAnAccess() and
    a.getEnclosingStmt() = s
  )
}

/** Holds if expression `e`'s enclosing statement assigns to `v`. */
predicate exprAssignsErrorVar(Expr e, ErrorVar v) {
  exists(Assignment a |
    a.getLValue() = v.getAnAccess() and
    (a = e or a.getAChild*() = e)
  )
}

/**
 * Holds if the basic-block-sequence reachable from the basic block containing
 * `errCall`, restricted to the same function and to the path that leads to
 * `gotoStmt`, contains no assignment to `v` before `gotoStmt`.
 *
 * We approximate this syntactically: within the same containing block / a few
 * sibling statements between `errCall` and `gotoStmt`, no assignment to `v`
 * appears.
 */
predicate noAssignBetween(ErrorLogCall errCall, GotoStmt gotoStmt, ErrorVar v) {
  // err call and goto must be inside the same enclosing block (typical "if (err) { dev_err(...); goto X; }" idiom)
  exists(BlockStmt b |
    b = errCall.getEnclosingStmt().getParentStmt*() and
    b = gotoStmt.getParentStmt*()
  ) and
  not exists(Assignment a |
    a.getLValue() = v.getAnAccess() and
    // assignment happens after the err call
    a.getLocation().getStartLine() >= errCall.getLocation().getStartLine() and
    a.getLocation().getStartLine() <= gotoStmt.getLocation().getStartLine() and
    a.getEnclosingFunction() = errCall.getEnclosingFunction()
  )
}

/**
 * The goto target label's block returns the error variable `v`
 * (i.e. somewhere reachable from the label there is `return v;`).
 */
predicate labelReturnsErrorVar(GotoStmt g, ErrorVar v) {
  exists(ReturnStmt r |
    r.getEnclosingFunction() = g.getEnclosingFunction() and
    r.getExpr().(VariableAccess).getTarget() = v and
    // the label is before the return (cleanup-then-return idiom)
    g.getTarget().getLocation().getStartLine() <= r.getLocation().getStartLine()
  )
}

/**
 * Holds if on the path from function entry to `errCall`, the error variable
 * `v` was last assigned 0 (or never assigned with a non-zero literal). The
 * simplest signal: the variable has an initializer of 0 and no prior
 * non-zero assignment dominates `errCall`.
 */
predicate retIsLikelyZeroAt(ErrorLogCall errCall, ErrorVar v) {
  v.getFunction() = errCall.getEnclosingFunction() and
  (
    // initializer is integer literal 0 (or absent — default-init may apply)
    not exists(v.getInitializer())
    or
    v.getInitializer().getExpr().getValue() = "0"
  )
}

from
  Function f, ErrorLogCall errCall, GotoStmt gotoStmt, ErrorVar v
where
  f = errCall.getEnclosingFunction() and
  f = gotoStmt.getEnclosingFunction() and
  f = v.getFunction() and
  f instanceof IntReturningFunction and
  // error is logged then a cleanup goto is taken in the same enclosing block
  noAssignBetween(errCall, gotoStmt, v) and
  // the cleanup label returns `v`
  labelReturnsErrorVar(gotoStmt, v) and
  // `v` was not previously set to a negative errno
  retIsLikelyZeroAt(errCall, v) and
  // the goto is syntactically after the err call
  gotoStmt.getLocation().getStartLine() >= errCall.getLocation().getStartLine() and
  gotoStmt.getLocation().getStartLine() - errCall.getLocation().getStartLine() <= 5
select gotoStmt,
  "Error is logged by $@ but no error code is assigned to '" + v.getName() +
    "' before this cleanup goto; function will return success.", errCall, errCall.toString()
