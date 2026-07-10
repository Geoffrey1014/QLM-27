/**
 * @name Function returns success (or stale value) on a failure-branch
 *       goto (error-return-code pattern)
 * @description Detects int-returning functions where:
 *                P1. a local `int ret`/`err`/`rc`/`error` flows to the
 *                    function's return value (initialized to 0);
 *                P2. an IfStmt's then-branch (direct or block) contains
 *                    a `goto cleanup` to that return path; and
 *                P3. the if-condition is NOT a check on the return
 *                    variable itself, and the then-branch does NOT
 *                    explicitly assign anything to the return variable
 *                    before the goto (so the variable is still 0).
 *              Under these conditions the function silently returns 0
 *              (success) on what is in fact a failure branch — the bug
 *              shape fixed by upstream commit 31d82c2c787d ("kernel:
 *              kexec_file: fix error return code of
 *              kexec_calculate_store_digests()") and by commits
 *              620b90d30c08, 45c7eaeb29d6 in the same family.
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3/c3/error-return-code-missing
 * @tags reliability
 *       error-handling
 *       correctness
 */

import cpp

/* P1 — function has a local int return variable (`ret`/`err`/...) that
 *      flows to the function's return value and is initialized to 0. */
predicate isErrReturnFunction(Function f, LocalVariable retVar) {
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

/* P3 — at this goto, the return variable still holds 0: the
 *      then-branch is either a bare `goto` (no preceding statements)
 *      or a block in which no statement before the goto assigns to
 *      the return variable. The if-condition itself is not a check
 *      on the return variable. */
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
          not a.getRValue().getValue() = "0"
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
       "caller will see success."
