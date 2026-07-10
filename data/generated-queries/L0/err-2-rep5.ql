/**
 * @name Function returns success on a failure-branch goto
 *       (error-return-code pattern) [L0 zero-shot single-predicate]
 * @description Detects int-returning functions where:
 *                P1. a local `int ret`/`err`/`rc`/`error` flows to the
 *                    function's return value
 *                    (helper predicate isErrReturnFunction); and
 *              (inlined in the assembly where-clause because L0
 *               limits us to a single named predicate):
 *                P2. an IfStmt's then-branch (direct or block) contains
 *                    a `goto cleanup` to that return path; and
 *                P3. the if-condition does NOT read the return variable
 *                    itself, and nothing earlier in the then-block
 *                    assigns a non-zero value to that variable before
 *                    the goto.
 *              Under these conditions the function may silently return a
 *              stale (possibly success) value on what is in fact a
 *              failure branch — the bug shape fixed by upstream commit
 *              45c7eaeb29d6 ("thermal: thermal_of: Fix error return
 *              code of thermal_of_populate_bind_params()").
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3/l0/error-return-code-missing
 * @tags reliability
 *       error-handling
 *       error-return
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

from Function f, LocalVariable retVar, GotoStmt g, IfStmt ifs
where
  isErrReturnFunction(f, retVar) and
  g.getEnclosingFunction() = f and
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
select g,
       "Function `" + f.getName() +
       "` jumps to cleanup with `" + retVar.getName() +
       "` not set to a non-zero error code on a failure branch — " +
       "caller may see success."
