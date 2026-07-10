/**
 * @name Function returns success (0) on a failure-branch goto
 *       (error-return-code pattern) [L0 zero-shot single-predicate]
 * @description Detects int-returning functions where:
 *                P1. a local `int ret = 0;` (or `int err = 0;`) flows to
 *                    the return value (helper predicate hasZeroInitRet); and
 *              (inlined in the assembly where-clause because L0 limits us
 *               to a single predicate):
 *                P2. an IfStmt's then-branch contains a `goto <label>`
 *                    that reaches the ret-returning tail; and
 *                P3. the if-condition does not read `ret` itself, and
 *                    nothing earlier in the then-block assigns a non-zero
 *                    value to `ret` before the goto.
 *              Under these conditions the function silently returns 0
 *              (success) on what is in fact a failure branch — the bug
 *              shape fixed by upstream commit 26594c6bbb60 ("rpmsg:
 *              qcom_glink_native: fix error return code of
 *              qcom_glink_rx_data()").
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3/l0/error-return-code-missing
 * @tags reliability
 *       error-handling
 *       error-return
 */

import cpp

/* P1 — function has `int ret = 0;` (or `int err = 0;`) whose value reaches a return. */
predicate hasZeroInitRet(Function f, LocalVariable retVar) {
  f.fromSource() and
  retVar.getFunction() = f and
  (retVar.getName() = "ret" or retVar.getName() = "err") and
  retVar.getType().getUnspecifiedType() instanceof IntType and
  retVar.getInitializer().getExpr().getValue() = "0" and
  exists(ReturnStmt rs |
    rs.getEnclosingFunction() = f and
    rs.getExpr().getAChild*().(VariableAccess).getTarget() = retVar
  )
}

from Function f, LocalVariable retVar, GotoStmt g, IfStmt ifs
where
  hasZeroInitRet(f, retVar) and
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
       "` reaches its cleanup goto with `" + retVar.getName() +
       "` still 0 on a failure branch — caller will see success."
