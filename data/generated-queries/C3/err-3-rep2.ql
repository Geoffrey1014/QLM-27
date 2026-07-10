/**
 * @name Error-return-code: goto to error label without assigning errno to ret
 * @description Function declares `int ret = 0;` and on a failure branch
 *              executes `goto LABEL;` that leads to `return ret;`, but the
 *              if-body containing the goto does not assign a non-zero value
 *              to `ret`. The function therefore returns success on the
 *              failure path. Mirrors the bug fixed by 26594c6bbb60c.
 * @kind problem
 * @problem.severity warning
 * @id qlm/err-return-code/26594c6
 */

import cpp

/* The function declares `int ret = 0;` (the value carried back to caller). */
predicate hasZeroInitRet(Function f, LocalVariable ret) {
  ret.getFunction() = f and
  ret.getType().getUnspecifiedType() instanceof IntType and
  ret.getInitializer().getExpr().getValue() = "0"
}

/* There exists a `return ret;` in the function (ret is the propagated value). */
predicate returnsRetVar(Function f, LocalVariable ret, ReturnStmt rs) {
  rs.getEnclosingFunction() = f and
  hasZeroInitRet(f, ret) and
  exists(VariableAccess va |
    va = ret.getAnAccess() and
    va.getParent*() = rs.getExpr()
  )
}

/* The goto target is reachable (via control-flow) to a `return ret`. */
predicate gotoReachesRetReturn(GotoStmt g, LocalVariable ret) {
  exists(Function f, ReturnStmt rs |
    f = g.getEnclosingFunction() and
    returnsRetVar(f, ret, rs) and
    g.getTarget().getASuccessor+() = rs
  )
}

/* The enclosing `if (...)` body assigns to `ret` before reaching the goto. */
predicate retAssignedInIfBeforeGoto(GotoStmt g, LocalVariable ret) {
  exists(IfStmt ifs, AssignExpr a |
    g.getParent*() = ifs and
    a.getEnclosingStmt().getParent*() = ifs and
    a.getLValue() = ret.getAnAccess() and
    a.getASuccessor+() = g
  )
}

from GotoStmt g, LocalVariable ret, Function f
where
  f = g.getEnclosingFunction() and
  hasZeroInitRet(f, ret) and
  /* The goto is inside an `if` body (failure-branch guard). */
  exists(IfStmt ifs | g.getParent*() = ifs) and
  /* The goto eventually returns `ret`. */
  gotoReachesRetReturn(g, ret) and
  /* And the if-body does NOT assign ret first. */
  not retAssignedInIfBeforeGoto(g, ret)
select g,
  "Error-return-code bug: goto on failure path in function `" + f.getName() +
  "` returns `" + ret.getName() +
  "` without assigning a non-zero errno first; function reports success."
