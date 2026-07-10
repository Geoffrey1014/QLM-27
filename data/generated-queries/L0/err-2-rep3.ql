/**
 * @name Function returns success (0) on a failure-branch goto
 *       (error-return-code missing pattern) [L0 zero-shot single-predicate]
 * @description Detects int-returning functions where:
 *                P1. a local int `ret` (or `err`/`rc`) flows to the
 *                    return value of the function
 *                    (helper predicate isRetReturnFunction); and
 *              (inlined in the assembly where-clause because L0
 *               limits us to a single predicate):
 *                P2. an IfStmt's then-branch contains a `goto cleanup`
 *                    targeting that return path;
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
 * @id qlm/rq3/l0/err-2-rep3
 * @tags reliability
 *       error-handling
 *       error-return
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

from Function f, LocalVariable retVar, GotoStmt g, IfStmt ifs
where
  isRetReturnFunction(f, retVar) and
  g.getEnclosingFunction() = f and
  (ifs.getThen() = g or ifs.getThen().(BlockStmt).getAStmt() = g) and
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
select g,
       "Function `" + f.getName() +
       "` jumps to cleanup with `" + retVar.getName() +
       "` not assigned a non-zero error code on a failure branch — " +
       "caller may see success."
