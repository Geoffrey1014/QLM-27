/**
 * @name Function returns success (0) on a failure-branch goto
 *       (error-return-code missing pattern)
 * @description Detects int-returning functions where:
 *                P1. a local int `ret` (or `err`/`rc`) flows to the
 *                    return value of the function;
 *                P2. an IfStmt's then-branch contains a `goto cleanup`
 *                    to that return path; and
 *                P3. the if-condition is NOT a check on `ret` itself,
 *                    and nothing in the then-branch assigns a non-zero
 *                    value to `ret` before the goto.
 *              Under these conditions the function may silently return
 *              0 (success) on what is in fact a failure branch — the
 *              bug shape fixed by upstream commit 45c7eaeb29d6
 *              ("thermal: thermal_of: Fix error return code of
 *              thermal_of_populate_bind_params()").
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3/c3/err-2-rep3
 * @tags reliability
 *       error-handling
 *       correctness
 */

import cpp

/* P1 — function returns the value of a local int named ret/err/rc. */
predicate isRetReturnFunction(Function f, LocalVariable retVar) {
  f.fromSource() and
  retVar.getFunction() = f and
  (retVar.getName() = "ret" or retVar.getName() = "err" or retVar.getName() = "rc") and
  retVar.getType().getUnspecifiedType() instanceof IntType and
  exists(ReturnStmt rs |
    rs.getEnclosingFunction() = f and
    rs.getExpr().(VariableAccess).getTarget() = retVar
  )
}

/* P2 — goto in the then-branch of an IfStmt (a failure-branch shortcut). */
predicate isFailureBranchGoto(GotoStmt g, IfStmt ifs) {
  ifs.getThen() = g or
  ifs.getThen().(BlockStmt).getAStmt() = g
}

/* P3 — at this goto, `ret` is not given a non-zero value in the then-block
 *      (and the if-condition is not on `ret` itself). */
predicate retNotSetInBranch(GotoStmt g, IfStmt ifs, LocalVariable retVar) {
  isFailureBranchGoto(g, ifs) and
  retVar.getFunction() = g.getEnclosingFunction() and
  not ifs.getCondition().getAChild*().(VariableAccess).getTarget() = retVar and
  (
    ifs.getThen() = g
    or
    not exists(Assignment a |
      a.getEnclosingStmt().getParent*() = ifs.getThen() and
      a.getLValue().(VariableAccess).getTarget() = retVar and
      (
        a.getRValue().getValue() != "0"
        or
        a.getRValue() instanceof UnaryMinusExpr
      )
    )
  )
}

from Function f, LocalVariable retVar, GotoStmt g, IfStmt ifs
where
  isRetReturnFunction(f, retVar) and
  g.getEnclosingFunction() = f and
  isFailureBranchGoto(g, ifs) and
  retNotSetInBranch(g, ifs, retVar)
select g,
       "Function `" + f.getName() +
       "` jumps to cleanup with `" + retVar.getName() +
       "` not assigned a non-zero error code on a failure branch — " +
       "caller may see success."
