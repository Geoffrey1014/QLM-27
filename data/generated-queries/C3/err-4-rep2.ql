/**
 * @name Function jumps to cleanup on a failure branch without setting status
 *       (error-return-code pattern)
 * @description Detects int-returning functions where:
 *                P1. a local `int status;` flows to the function's return value;
 *                P2. an IfStmt's then-branch contains a `goto cleanup`
 *                    to that return path; and
 *                P3. the if-condition is NOT a check on `status` itself, and
 *                    nothing in the then-branch assigns a value to
 *                    `status` before the goto.
 *              Under these conditions the function can silently propagate
 *              whatever value `status` already held (typically 0 from an
 *              earlier successful call) on what is in fact a failure
 *              branch — the bug shape fixed by upstream commit
 *              c021e0235770 ("usb: gadget: legacy: fix error return code
 *              of multi_bind()").
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3/c3/error-return-code-status-missing
 * @tags reliability
 *       error-handling
 *       correctness
 */

import cpp

/* P1 — function has a local `int status;` whose value flows to its
 *      return expression. */
predicate isStatusReturnFunction(Function f, LocalVariable statusVar) {
  f.fromSource() and
  statusVar.getFunction() = f and
  statusVar.getName() = "status" and
  statusVar.getType().getUnspecifiedType() instanceof IntType and
  exists(ReturnStmt rs |
    rs.getEnclosingFunction() = f and
    rs.getExpr().(VariableAccess).getTarget() = statusVar
  )
}

/* P2 — goto in the then-branch of an IfStmt (a failure-branch shortcut). */
predicate isFailureBranchGoto(GotoStmt g, Function f) {
  g.getEnclosingFunction() = f and
  exists(IfStmt ifs |
    ifs.getThen() = g or
    ifs.getThen().(BlockStmt).getStmt(0) = g
  )
}

/* P3 — at this goto, `status` has not been (re)assigned in the
 *      then-branch and the if-condition itself doesn't read `status`
 *      (so the branch is a fresh failure check, not a relay of an
 *      already-failed status). */
predicate statusNotSetOnFailureBranch(GotoStmt g, LocalVariable statusVar) {
  statusVar.getName() = "status" and
  statusVar.getFunction() = g.getEnclosingFunction() and
  exists(IfStmt ifs |
    (ifs.getThen() = g or ifs.getThen().(BlockStmt).getStmt(_) = g) and
    not ifs.getCondition().getAChild*().(VariableAccess).getTarget() = statusVar and
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
          a.getLValue().(VariableAccess).getTarget() = statusVar
        )
      )
    )
  )
}

from Function f, LocalVariable statusVar, GotoStmt g
where
  isStatusReturnFunction(f, statusVar) and
  g.getEnclosingFunction() = f and
  isFailureBranchGoto(g, f) and
  statusNotSetOnFailureBranch(g, statusVar)
select g,
       "Function `" + f.getName() +
       "` jumps to cleanup with `status` not assigned on a failure branch — " +
       "caller may see success."
