/**
 * @name Missing error code on early-exit goto in cleanup-style function
 * @description A function declares an error variable initialized to 0 and uses a
 *              `goto cleanup`-style early-exit pattern on a failure condition
 *              (e.g. NULL check after a getter), but does not assign a negative
 *              errno to that variable before jumping. The function later returns
 *              the variable, so the caller silently observes success on a real
 *              failure path.
 * @kind problem
 * @problem.severity warning
 * @id cpp/missing-errno-on-goto-cleanup
 * @tags correctness
 *       reliability
 */

import cpp
import semmle.code.cpp.controlflow.Guards

/**
 * A local variable used as the function's error-return holder:
 *   - integer-typed
 *   - initialized to 0 (or assigned 0 before any other write)
 *   - eventually returned by the enclosing function
 */
predicate isErrHolder(LocalVariable v, Function f) {
  v.getFunction() = f and
  v.getType().getUnderlyingType() instanceof IntegralType and
  // initialized literally to 0
  exists(Expr init | init = v.getInitializer().getExpr() | init.getValue().toInt() = 0) and
  // f returns v somewhere
  exists(ReturnStmt r, VariableAccess va |
    r.getEnclosingFunction() = f and
    va = r.getExpr().(VariableAccess) and
    va.getTarget() = v
  )
}

/**
 * An `if (!x) goto L;` style statement (also matches `if (x == NULL) goto L;`
 * and `if (IS_ERR(x)) goto L;`), inside function `f`, that does not assign
 * the err holder along the goto edge.
 */
predicate badGotoBranch(IfStmt ifs, GotoStmt gs, LocalVariable err, Function f) {
  ifs.getEnclosingFunction() = f and
  isErrHolder(err, f) and
  // The "then" branch is (or contains as its sole statement) a goto
  (
    gs = ifs.getThen()
    or
    exists(BlockStmt b |
      b = ifs.getThen() and
      gs = b.getStmt(0) and
      b.getNumStmt() = 1
    )
  ) and
  // condition looks like a failure test (NULL / IS_ERR / negation / equality to 0)
  exists(Expr cond | cond = ifs.getCondition() |
    cond instanceof NotExpr
    or
    cond.(EQExpr).getAnOperand().getValue().toInt() = 0
    or
    exists(FunctionCall fc |
      fc = cond.(FunctionCall) and
      fc.getTarget().getName().regexpMatch("IS_ERR.*")
    )
    or
    exists(FunctionCall fc, NotExpr ne |
      ne = cond and
      fc = ne.getOperand() and
      fc.getTarget().getName().regexpMatch(".*(get|alloc|find|lookup|create|parse|of_).*")
    )
  ) and
  // No assignment to err inside the then-branch
  not exists(Assignment a |
    a.getEnclosingStmt().getParentStmt*() = ifs.getThen() and
    a.getLValue().(VariableAccess).getTarget() = err
  )
}

/**
 * The goto target label leads (directly) to a return of err, with no
 * intervening assignment to err between the label and the return.
 */
predicate labelReturnsErrUnchanged(GotoStmt gs, LocalVariable err) {
  exists(LabelStmt lbl, ReturnStmt ret |
    lbl = gs.getTarget() and
    ret.getEnclosingFunction() = gs.getEnclosingFunction() and
    ret.getExpr().(VariableAccess).getTarget() = err and
    // The label is reachable to the return without err being reassigned.
    // Approximation: there exists no assignment to err in any statement
    // between the label and the return in source order in the same function.
    not exists(Assignment a |
      a.getEnclosingFunction() = gs.getEnclosingFunction() and
      a.getLValue().(VariableAccess).getTarget() = err and
      a.getLocation().getStartLine() > lbl.getLocation().getStartLine() and
      a.getLocation().getStartLine() < ret.getLocation().getStartLine()
    )
  )
}

from IfStmt ifs, GotoStmt gs, LocalVariable err, Function f
where
  badGotoBranch(ifs, gs, err, f) and
  labelReturnsErrUnchanged(gs, err) and
  // err must still be 0 when returned: its initializer is 0 and no assignment
  // along the bad branch (already enforced by badGotoBranch's not-exists).
  not f.getName().regexpMatch("(?i).*(test|debug).*")
select ifs,
  "Early-exit '" + gs.toString() + "' to a cleanup label that returns '" + err.getName() +
    "' without first setting it to a negative errno, in function $@.", f, f.getName()
