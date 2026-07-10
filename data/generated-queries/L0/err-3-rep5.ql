/**
 * @name Function returns success (0) on a failure-branch goto
 *       (error-return-code pattern) [L0 zero-shot single-predicate]
 * @description Detects int-returning functions where:
 *                P1. a local status variable (`ret`, `err`, `rc`, `error`)
 *                    is initialized to 0 and flows to the return value
 *                    (helper predicate isErrReturnFunction); and
 *              (inlined in the assembly where-clause because L0
 *               limits us to a single predicate):
 *                P2. an IfStmt's then-branch contains a `goto cleanup`
 *                    targeting that return path; and
 *                P3. the if-condition does not read the status variable
 *                    itself, and nothing earlier in the then-block assigns
 *                    a value to that variable before the goto.
 *              Under these conditions the function silently returns 0
 *              (success) on what is in fact a failure branch — the bug
 *              shape fixed by upstream commit 26594c6bbb60 ("rpmsg:
 *              qcom_glink_native: fix error return code of
 *              qcom_glink_rx_data()").
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3/l0/err-3-rep5/error-return-code-missing
 * @tags reliability
 *       error-handling
 *       error-return
 */

import cpp

/* P1 — function has `int <status> = 0;` that flows to its return value. */
predicate isErrReturnFunction(Function f, LocalVariable errVar) {
  f.fromSource() and
  errVar.getFunction() = f and
  (errVar.getName() = "ret" or
   errVar.getName() = "err" or
   errVar.getName() = "rc" or
   errVar.getName() = "error") and
  errVar.getType().getUnspecifiedType() instanceof IntType and
  exists(ReturnStmt rs |
    rs.getEnclosingFunction() = f and
    rs.getExpr().(VariableAccess).getTarget() = errVar
  ) and
  errVar.getInitializer().getExpr().getValue() = "0"
}

from Function f, LocalVariable errVar, GotoStmt g, IfStmt ifs
where
  isErrReturnFunction(f, errVar) and
  g.getEnclosingFunction() = f and
  (ifs.getThen() = g or ifs.getThen().(BlockStmt).getStmt(_) = g) and
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
        a.getLValue().(VariableAccess).getTarget() = errVar
      )
    )
  )
select g,
       "Function `" + f.getName() +
       "` jumps to cleanup with `" + errVar.getName() +
       "` still 0 on a failure branch — caller will see success."
