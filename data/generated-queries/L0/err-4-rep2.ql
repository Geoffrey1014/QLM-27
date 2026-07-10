/**
 * @name Function jumps to cleanup on a failure branch without setting status
 *       (error-return-code pattern) [L0 zero-shot single-predicate]
 * @description Detects int-returning functions where:
 *                P1. a local `int status;` flows to the return value
 *                    (helper predicate isStatusReturnFunction); and
 *              (inlined in the assembly where-clause because L0
 *               limits us to a single predicate):
 *                P2. an IfStmt's then-branch contains a `goto cleanup`
 *                    targeting that return path;
 *                P3. the if-condition does not read `status` itself, and
 *                    nothing earlier in the then-block assigns a value to
 *                    `status` before the goto.
 *              Under these conditions the function can silently propagate
 *              whatever value `status` already held (typically 0 from an
 *              earlier successful call) on what is in fact a failure
 *              branch — the bug shape fixed by upstream commit
 *              c021e0235770 ("usb: gadget: legacy: fix error return code
 *              of multi_bind()").
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3/l0/error-return-code-status-missing
 * @tags reliability
 *       error-handling
 *       error-return
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

from Function f, LocalVariable statusVar, GotoStmt g, IfStmt ifs
where
  isStatusReturnFunction(f, statusVar) and
  g.getEnclosingFunction() = f and
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
select g,
       "Function `" + f.getName() +
       "` jumps to cleanup with `status` not assigned on a failure branch — " +
       "caller may see success."
