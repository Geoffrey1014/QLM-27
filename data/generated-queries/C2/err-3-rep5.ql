/**
 * @name  rq3-c2-err-3-rep5
 * @id    cpp/rq3/c2/err-3-rep5
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects missing error-code assignment before a goto on an
 *              error path: a function returns an int status variable, an
 *              if-guard models an error condition whose then-branch jumps
 *              via goto to a common exit, yet no negative error code is
 *              assigned to the return variable in that branch.
 */

import cpp

/**
 * Holds if `f` returns `int` and has a local variable `ret` that is used
 * as the function's return value (returned at least once unmodified by a
 * direct `return ret;` statement).
 */
predicate returnsErrorCode(Function f, LocalVariable ret) {
  f.getType().getUnspecifiedType() instanceof IntType and
  ret.getFunction() = f and
  ret.getType().getUnspecifiedType() instanceof IntType and
  exists(ReturnStmt r, VariableAccess va |
    r.getEnclosingFunction() = f and
    va = r.getExpr() and
    va.getTarget() = ret
  )
}

/**
 * Holds if `ifs` is an if-statement inside `f` whose then-branch contains
 * a `goto` statement (typically jumping to a common cleanup/exit label).
 */
predicate isErrorCheckGoto(Function f, IfStmt ifs, GotoStmt g) {
  ifs.getEnclosingFunction() = f and
  g.getEnclosingFunction() = f and
  g.getParent+() = ifs.getThen()
}

/**
 * Holds if the goto `g` targets a label whose successor path includes a
 * `return ret;` statement.
 */
predicate gotoTargetReturnsVar(GotoStmt g, LocalVariable ret) {
  exists(ReturnStmt r, VariableAccess va |
    r.getEnclosingFunction() = g.getEnclosingFunction() and
    va = r.getExpr() and
    va.getTarget() = ret
  )
}

/**
 * Holds if, within the then-branch of `ifs`, there is no assignment that
 * writes to `ret` before the goto `g`. This captures the "forgot to set
 * the error code" smell.
 */
predicate noAssignmentBeforeGoto(IfStmt ifs, GotoStmt g, LocalVariable ret) {
  g.getParent+() = ifs.getThen() and
  not exists(Assignment a |
    a.getParent+() = ifs.getThen() and
    a.getLValue().(VariableAccess).getTarget() = ret
  )
}

from Function f, LocalVariable ret, IfStmt ifs, GotoStmt g
where
  returnsErrorCode(f, ret) and
  isErrorCheckGoto(f, ifs, g) and
  gotoTargetReturnsVar(g, ret) and
  noAssignmentBeforeGoto(ifs, g, ret)
select ifs,
  "Error path goto without assigning error code to return variable '" +
    ret.getName() + "'."
