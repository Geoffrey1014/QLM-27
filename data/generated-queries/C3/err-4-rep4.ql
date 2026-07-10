/**
 * @name Function returns success (0) on a failure-branch goto
 *       (error-return-code pattern)
 * @description Detects int-returning functions where:
 *                P1. a local `int <var> = 0;` flows to the return value;
 *                P2. an IfStmt's then-branch contains a `goto cleanup`
 *                    to the function's return-status path; and
 *                P3. the if-condition is NOT a check on that variable
 *                    itself, and nothing in the then-branch assigns a
 *                    non-zero value to it before the goto.
 *              Under these conditions the function silently returns 0
 *              (success) on what is actually a failure branch -- the bug
 *              shape fixed by upstream commit c021e0235770 ("usb: gadget:
 *              legacy: fix error return code of multi_bind()").
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3/c3/error-return-code-missing-err-4-rep4
 * @tags reliability
 *       error-handling
 *       correctness
 */

import cpp

/* P1 -- function has `int <var> = 0;` that flows to its return value. */
predicate isStatusReturnFunction(Function f, LocalVariable statusVar) {
  f.fromSource() and
  statusVar.getFunction() = f and
  statusVar.getType().getUnspecifiedType() instanceof IntType and
  exists(ReturnStmt rs |
    rs.getEnclosingFunction() = f and
    rs.getExpr().(VariableAccess).getTarget() = statusVar
  ) and
  statusVar.getInitializer().getExpr().getValue() = "0"
}

/* P2 -- goto sits in the then-branch of an IfStmt. */
predicate isFailureBranchGoto(GotoStmt g, IfStmt ifs) {
  ifs.getEnclosingFunction() = g.getEnclosingFunction() and
  (
    ifs.getThen() = g or
    ifs.getThen().(BlockStmt).getStmt(_) = g
  )
}

/* P3 -- at this goto, `status` is still 0 (no non-zero assignment in the
 *      then-block before the goto, and the if-condition is not on status). */
predicate statusUnsetAtGoto(GotoStmt g, IfStmt ifs, LocalVariable statusVar) {
  isFailureBranchGoto(g, ifs) and
  statusVar.getFunction() = g.getEnclosingFunction() and
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
}

from Function f, LocalVariable statusVar, GotoStmt g, IfStmt ifs
where
  isStatusReturnFunction(f, statusVar) and
  g.getEnclosingFunction() = f and
  isFailureBranchGoto(g, ifs) and
  statusUnsetAtGoto(g, ifs, statusVar)
select g,
       "Function `" + f.getName() +
       "` jumps to cleanup with `" + statusVar.getName() +
       "` still 0 on a failure branch -- caller will see success."
