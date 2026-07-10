/**
 * @name Function returns success (or stale value) on a failure-branch
 *       goto (error-return-code pattern)
 * @description Detects int-returning functions where:
 *                P1. a local `int ret`/`err` flows to the return value;
 *                P2. an IfStmt's then-branch (direct or block) contains
 *                    a `goto cleanup` to that return path; and
 *                P3. the if-condition is NOT a check on the return
 *                    variable itself, and nothing in the then-branch
 *                    assigns a non-zero value to the return variable
 *                    before the goto.
 *              Under these conditions the function may silently return
 *              a stale (possibly success) value on what is in fact a
 *              failure branch — the bug shape fixed by upstream
 *              commit 45c7eaeb29d6 ("thermal: thermal_of: Fix error
 *              return code of thermal_of_populate_bind_params()") and
 *              by commit 620b90d30c08 ("mtd: maps: fix error return
 *              code of physmap_flash_remove()").
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3/c3/error-return-code-missing
 * @tags reliability
 *       error-handling
 *       correctness
 */

import cpp

/* P1 — function has a local int return variable (`ret`/`err`/...) that
 *      flows to the function's return value. */
predicate isErrReturnFunction(Function f, LocalVariable retVar) {
  f.fromSource() and
  retVar.getFunction() = f and
  retVar.getName() in ["ret", "err", "rc", "error"] and
  retVar.getType().getUnspecifiedType() instanceof IntType and
  exists(ReturnStmt rs |
    rs.getEnclosingFunction() = f and
    rs.getExpr().(VariableAccess).getTarget() = retVar
  )
}

/* P2 — goto in the then-branch (direct or anywhere in then-block) of
 *      an IfStmt (a failure-branch shortcut). */
predicate isFailureBranchGoto(GotoStmt g, Function f) {
  g.getEnclosingFunction() = f and
  exists(IfStmt ifs |
    ifs.getThen() = g
    or
    ifs.getThen().(BlockStmt).getAStmt() = g
  )
}

/* P3 — at this goto, the return variable still holds its prior
 *      (possibly success) value: no non-zero assignment in the then
 *      before the goto, and the if-condition is not on the variable
 *      itself. */
predicate errIsZeroAtGoto(GotoStmt g, LocalVariable retVar) {
  retVar.getName() in ["ret", "err", "rc", "error"] and
  retVar.getFunction() = g.getEnclosingFunction() and
  exists(IfStmt ifs |
    (ifs.getThen() = g or ifs.getThen().(BlockStmt).getAStmt() = g) and
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
  isErrReturnFunction(f, retVar) and
  g.getEnclosingFunction() = f and
  isFailureBranchGoto(g, f) and
  errIsZeroAtGoto(g, retVar)
select g,
       "Function `" + f.getName() +
       "` jumps to cleanup with `" + retVar.getName() +
       "` not set to a non-zero error code on a failure branch — " +
       "caller may see success."
