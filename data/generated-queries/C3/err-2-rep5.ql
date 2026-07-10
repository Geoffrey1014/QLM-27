/**
 * @name Error-return-code bug: goto to cleanup label without setting ret
 * @description Detects a goto statement targeting a cleanup label that
 *              returns `ret`, where the enclosing error-branch if-block
 *              does not first assign a negative errno to ret. This is
 *              the QLM error-return-code pattern (CWE-394) -- the
 *              function silently returns the previous (success) value
 *              of ret out of an error path.
 *
 *              Seed: thermal: thermal_of: Fix error return code of
 *              thermal_of_populate_bind_params() (45c7eaeb29d6)
 *
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3/c3/err-2-rep5
 * @tags reliability
 *       error-handling
 */

import cpp

predicate isErrorCleanupLabel(LabelStmt l) {
  exists(string n | n = l.getName() |
    n = "end" or n = "out" or n = "err" or n = "fail" or n = "cleanup" or
    n.matches("err\\_%") or n.matches("out\\_%") or n.matches("fail\\_%") or
    n.matches("free\\_%")
  )
}

predicate labelReturnsRet(LabelStmt l, LocalScopeVariable ret) {
  isErrorCleanupLabel(l) and
  ret.getName() = "ret" and
  exists(Function f, ReturnStmt r, VariableAccess va |
    f = l.getEnclosingFunction() and
    f = r.getEnclosingFunction() and
    f = ret.getFunction() and
    va = r.getExpr() and
    va.getTarget() = ret
  )
}

predicate gotoInErrorCondition(GotoStmt g) {
  exists(IfStmt ifs, Expr cond |
    ifs = g.getParent+() and
    cond = ifs.getCondition() and
    g = ifs.getThen().(Stmt).getChildStmt*()
  |
    cond instanceof NotExpr or
    exists(EQExpr eq | eq = cond and eq.getAnOperand().getValue() = "0") or
    exists(LTExpr lt | lt = cond and lt.getRightOperand().getValue() = "0") or
    exists(LEExpr le | le = cond and le.getRightOperand().getValue() = "0")
  )
}

predicate gotoMissingRetAssign(GotoStmt g, LocalScopeVariable ret) {
  exists(LabelStmt target, IfStmt ifs |
    target = g.getTarget() and
    labelReturnsRet(target, ret) and
    gotoInErrorCondition(g) and
    ifs = g.getParent+() and
    ifs.getEnclosingFunction() = g.getEnclosingFunction() and
    g = ifs.getThen().(Stmt).getChildStmt*() and
    not exists(Assignment a, VariableAccess lhs |
      a.getParent+() = ifs.getThen() and
      lhs = a.getLValue() and
      lhs.getTarget() = ret
    )
  )
}

from GotoStmt g, LocalScopeVariable ret, Function f
where gotoMissingRetAssign(g, ret) and f = g.getEnclosingFunction()
select g,
  "error-return-code bug: `goto " + g.getName() + "` jumps to a cleanup label that returns `" +
    ret.getName() + "` without first assigning a negative errno; function `" +
    f.getName() + "` will leak a success/stale value out of an error path."
