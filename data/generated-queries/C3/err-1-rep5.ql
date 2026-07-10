/**
 * @name Function returns success (0) on a failure-branch goto
 *       (error-return-code pattern)
 * @description Detects int-returning functions where:
 *                P1. a local `int err = 0;` flows to the return value;
 *                P2. an IfStmt's then-branch contains a `goto cleanup`
 *                    leading to that return path; and
 *                P3. the if-condition is NOT a check on `err` itself,
 *                    and nothing in the then-branch assigns a non-zero
 *                    value to `err` before the goto.
 *              In that configuration the function silently returns 0
 *              (success) on a branch that is in fact a failure path --
 *              the bug shape fixed by upstream commit 620b90d30c08
 *              ("mtd: maps: fix error return code of
 *              physmap_flash_remove()").
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3/c3/err-1-rep5/error-return-code-missing
 * @tags reliability
 *       error-handling
 *       correctness
 */

import cpp

/* P1 -- function has `int err = 0;` flowing to its return value. */
predicate hasErrReturnVar(Function f, LocalVariable errVar) {
  f.fromSource() and
  errVar.getFunction() = f and
  errVar.getName() = "err" and
  errVar.getType().getUnspecifiedType() instanceof IntType and
  errVar.getInitializer().getExpr().getValue() = "0" and
  exists(ReturnStmt rs |
    rs.getEnclosingFunction() = f and
    rs.getExpr().(VariableAccess).getTarget() = errVar
  )
}

/* P2 -- goto sits inside the then-branch of an IfStmt. */
predicate thenBranchGoto(IfStmt ifs, GotoStmt g) {
  ifs.getThen() = g or ifs.getThen().(BlockStmt).getStmt(_) = g
}

/* P3 -- at this goto, `err` is still 0: the if-condition does not
 *       read `err`, and no statement before the goto in the same
 *       then-block assigns a non-zero value to `err`.
 */
predicate errUntouchedOnBranch(IfStmt ifs, GotoStmt g, LocalVariable errVar) {
  thenBranchGoto(ifs, g) and
  errVar.getName() = "err" and
  errVar.getFunction() = g.getEnclosingFunction() and
  not ifs.getCondition().getAChild*().(VariableAccess).getTarget() = errVar and
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
        a.getLValue().(VariableAccess).getTarget() = errVar and
        a.getRValue().getValue() != "0"
      )
    )
  )
}

from Function f, LocalVariable errVar, IfStmt ifs, GotoStmt g
where
  hasErrReturnVar(f, errVar) and
  g.getEnclosingFunction() = f and
  thenBranchGoto(ifs, g) and
  errUntouchedOnBranch(ifs, g, errVar)
select g,
       "Function `" + f.getName() +
       "` jumps to cleanup with `err` still 0 on a failure branch -- " +
       "caller will see success on an actual error."
