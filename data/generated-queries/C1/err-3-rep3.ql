/**
 * @name Missing error code assignment before goto cleanup
 * @description An error condition triggers a goto to a cleanup label, but the
 *              status variable that the function ultimately returns is never
 *              reassigned to a non-zero error code. The function therefore
 *              returns 0 (success) on the error path.
 * @kind problem
 * @problem.severity warning
 * @id qlm/c1-err-3
 */

import cpp

/**
 * Holds if `v` is initialized to the integer literal 0 at its declaration.
 */
predicate initializedToZero(LocalVariable v) {
  exists(Expr init |
    init = v.getInitializer().getExpr() and
    init.getValue().toInt() = 0
  )
}

/**
 * Holds if `v` is ever assigned a non-zero constant or a unary-minus of a
 * constant (e.g. `-ENOENT`) anywhere in `f`.
 */
predicate assignedNonZero(LocalVariable v, Function f) {
  exists(Assignment a |
    a.getEnclosingFunction() = f and
    a.getLValue() = v.getAnAccess() and
    (
      a.getRValue().getValue().toInt() != 0
      or
      a.getRValue() instanceof UnaryMinusExpr
      or
      // any non-literal rvalue counts as "assigned"
      not exists(a.getRValue().getValue())
    )
  )
}

/**
 * Holds if `ret` is the variable that is returned by a `return ret;` in `f`.
 */
predicate isReturnedVar(LocalVariable v, Function f) {
  exists(ReturnStmt r |
    r.getEnclosingFunction() = f and
    r.getExpr() = v.getAnAccess()
  )
}

/**
 * A `goto` statement that jumps to a label inside the same function, used
 * as part of an error / cleanup path (taken from inside an `if`).
 */
class ErrorGoto extends GotoStmt {
  ErrorGoto() {
    exists(IfStmt ifs | ifs.getThen() = this.getParent*())
  }
}

/**
 * Holds if between `goto` statement `g` and `return ret;` (control falls
 * through the label to the return), variable `ret` is NOT assigned.
 *
 * Approximated structurally: in the basic block reachable from `g`'s target
 * up to the return statement, there is no Assignment writing to `ret`.
 */
predicate noAssignInThen(IfStmt ifs, LocalVariable ret) {
  not exists(VariableAccess va |
    va = ret.getAnAccess() and
    va.isModified() and
    va.getEnclosingStmt().getParent*() = ifs.getThen()
  )
}

from Function f, LocalVariable ret, ErrorGoto g, ReturnStmt r, IfStmt ifs
where
  ret.getFunction() = f and
  g.getEnclosingFunction() = f and
  r.getEnclosingFunction() = f and
  initializedToZero(ret) and
  isReturnedVar(ret, f) and
  // The goto sits in an if-then that contains no assignment to ret.
  ifs.getEnclosingFunction() = f and
  ifs.getThen() = g.getParent*() and
  noAssignInThen(ifs, ret) and
  // Heuristic: the if-condition is a "negative" check (error detection),
  // typified by `!x` or `x == NULL` / `x < 0` style. Filter to those
  // looking like error conditions.
  (
    ifs.getCondition() instanceof NotExpr or
    ifs.getCondition().(EqualityOperation).getAnOperand() instanceof Literal or
    ifs.getCondition() instanceof RelationalOperation
  ) and
  // The goto target is BEFORE the return — i.e. label is between goto and
  // return — so falling through the label reaches the return.
  exists(Stmt target | target = g.getTarget() and target.getLocation().getStartLine() < r.getLocation().getStartLine() and target.getLocation().getStartLine() > g.getLocation().getStartLine())
select g,
  "Error path takes 'goto " + g.getTarget().toString() +
    "' but the returned status variable '" + ret.getName() +
    "' is never assigned a non-zero error code, so the function returns success on this error path."
