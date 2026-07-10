/**
 * @name Function returns success (0) on a failure-branch goto
 *       (error-return-code pattern)
 * @description Detects int-returning functions where:
 *                P1. a local return-code variable (status / err / ret / rc /
 *                    error) is initialised to 0 and flows to the return
 *                    value;
 *                P2. an IfStmt's then-branch contains a `goto cleanup`
 *                    to that return path; and
 *                P3. the if-condition is NOT a check on the return-code
 *                    variable itself, and nothing in the then-branch
 *                    assigns a non-zero value to that variable before
 *                    the goto.
 *              Under these conditions the function silently returns 0
 *              (success) on what is in fact a failure branch — the bug
 *              shape fixed by upstream commit c021e0235770 ("usb: gadget:
 *              legacy: fix error return code of multi_bind()").
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3/c3/error-return-code-missing-err4
 * @tags reliability
 *       error-handling
 *       correctness
 */

import cpp

/* P1 — function has a local return-code variable initialised to 0 that
 *      flows to its return value. Variable name matches the conventional
 *      kernel return-code identifiers. */
predicate isStatusReturnFunction(Function f, LocalVariable statusVar) {
  f.fromSource() and
  statusVar.getFunction() = f and
  (statusVar.getName() = "status" or
   statusVar.getName() = "err" or
   statusVar.getName() = "ret" or
   statusVar.getName() = "rc" or
   statusVar.getName() = "error") and
  statusVar.getType().getUnspecifiedType() instanceof IntType and
  exists(ReturnStmt rs |
    rs.getEnclosingFunction() = f and
    rs.getExpr().(VariableAccess).getTarget() = statusVar
  ) and
  statusVar.getInitializer().getExpr().getValue() = "0"
}

/* P2 — goto in the then-branch of an IfStmt (a failure-branch shortcut). */
predicate isFailureBranchGoto(GotoStmt g, Function f) {
  g.getEnclosingFunction() = f and
  exists(IfStmt ifs |
    ifs.getThen() = g or
    ifs.getThen().(BlockStmt).getStmt(0) = g
  )
}

/* P3 — at this goto, the return-code variable is still 0 (no non-zero
 *      assignment in the then before the goto, and the if-condition is
 *      not on that variable itself). */
predicate statusIsZeroAtGoto(GotoStmt g, LocalVariable statusVar) {
  (statusVar.getName() = "status" or
   statusVar.getName() = "err" or
   statusVar.getName() = "ret" or
   statusVar.getName() = "rc" or
   statusVar.getName() = "error") and
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
          a.getLValue().(VariableAccess).getTarget() = statusVar and
          a.getRValue().getValue() != "0"
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
  statusIsZeroAtGoto(g, statusVar)
select g,
       "Function `" + f.getName() +
       "` jumps to cleanup with `" + statusVar.getName() +
       "` still 0 on a failure branch — caller will see success."
