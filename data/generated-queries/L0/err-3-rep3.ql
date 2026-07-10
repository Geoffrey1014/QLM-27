/**
 * @name Function returns success (0) on a failure-branch goto
 *       (error-return-code pattern)
 * @description Detects int-returning functions where a local `int ret = 0;`
 *              (or err/rc) flows to the return value, and an IfStmt's
 *              then-branch contains a `goto cleanup` without first
 *              assigning a non-zero value to the return-var, and the
 *              if-condition is not itself a check on the return-var.
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
 *       correctness
 */

import cpp

/* Single L0 predicate — an int-returning function whose local `ret`/`err`/`rc`
 * is initialized to 0 and flows to a ReturnStmt. All remaining logic (goto in
 * failure-branch then-block with no non-zero assignment to errVar before it,
 * and if-condition not on errVar) is inlined in the assembly. */
predicate isErrReturnFunction(Function f, LocalVariable errVar) {
  f.fromSource() and
  errVar.getFunction() = f and
  (errVar.getName() = "ret" or errVar.getName() = "err" or errVar.getName() = "rc") and
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
        a.getLValue().(VariableAccess).getTarget() = errVar and
        a.getRValue().getValue() != "0"
      )
    )
  )
select g,
       "Function `" + f.getName() +
       "` jumps to cleanup with `" + errVar.getName() +
       "` still 0 on a failure branch — caller will see success."
