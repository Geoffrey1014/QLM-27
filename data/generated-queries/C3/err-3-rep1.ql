/**
 * @name Function returns success (0) on a failure-branch goto
 *       (error-return-code pattern)
 * @description Detects int-returning functions where:
 *                P1. a local `int ret = 0;` (or err/rc/error) flows to
 *                    the function's return value;
 *                P2. an IfStmt's then-branch contains a `goto cleanup`
 *                    to that return path; and
 *                P3. the if-condition is NOT a check on the ret variable
 *                    itself, and nothing in the then-branch assigns a
 *                    non-zero value to ret before the goto.
 *              Under these conditions the function silently returns 0
 *              (success) on what is in fact a failure branch — the bug
 *              shape fixed by upstream commit 26594c6bbb60 ("rpmsg:
 *              qcom_glink_native: fix error return code of
 *              qcom_glink_rx_data()").
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3/c3/error-return-code-missing-err3
 * @tags reliability
 *       error-handling
 *       correctness
 */

import cpp

/* P1 — function has `int ret = 0;` (or err/rc/error) that flows to its
 *      return value. */
predicate isRetReturnFunction(Function f, LocalVariable retVar) {
  f.fromSource() and
  retVar.getFunction() = f and
  retVar.getName() in ["ret", "err", "rc", "error"] and
  retVar.getType().getUnspecifiedType() instanceof IntType and
  exists(ReturnStmt rs |
    rs.getEnclosingFunction() = f and
    rs.getExpr().(VariableAccess).getTarget() = retVar
  ) and
  retVar.getInitializer().getExpr().getValue() = "0"
}

/* P2 — goto in the then-branch of an IfStmt (a failure-branch shortcut). */
predicate isFailureBranchGoto(GotoStmt g, Function f) {
  g.getEnclosingFunction() = f and
  exists(IfStmt ifs |
    ifs.getThen() = g or
    ifs.getThen().(BlockStmt).getStmt(_) = g
  )
}

/* P3 — at this goto, the ret variable is still 0:
 *      no non-zero assignment in the then-block before the goto,
 *      and the if-condition is not on the ret variable itself. */
predicate retIsZeroAtGoto(GotoStmt g, LocalVariable retVar) {
  retVar.getName() in ["ret", "err", "rc", "error"] and
  retVar.getFunction() = g.getEnclosingFunction() and
  exists(IfStmt ifs |
    (ifs.getThen() = g or ifs.getThen().(BlockStmt).getStmt(_) = g) and
    not ifs.getCondition().getAChild*().(VariableAccess).getTarget() = retVar and
    (
      ifs.getThen() = g
      or
      exists(BlockStmt blk, int gi |
        ifs.getThen() = blk and
        blk.getStmt(gi) = g and
        not exists(int j, ExprStmt es, Assignment a |
          j < gi and
          blk.getStmt(j) = es and
          es.getExpr() = a and
          a.getLValue().(VariableAccess).getTarget() = retVar and
          a.getRValue().getValue() != "0"
        )
      )
    )
  )
}

from Function f, LocalVariable retVar, GotoStmt g
where
  isRetReturnFunction(f, retVar) and
  g.getEnclosingFunction() = f and
  isFailureBranchGoto(g, f) and
  retIsZeroAtGoto(g, retVar)
select g,
       "Function `" + f.getName() +
       "` jumps to cleanup with `" + retVar.getName() +
       "` still 0 on a failure branch — caller will see success."
