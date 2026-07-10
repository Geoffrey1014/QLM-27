/**
 * @name Function returns success (0) on a failure-branch goto
 *       (error-return-code pattern)
 * @description Detects int-returning functions where a local `int err = 0;`
 *              flows to the return value, and an IfStmt's then-branch
 *              contains a `goto cleanup` without first assigning a non-zero
 *              value to `err`, and the if-condition is not itself an err
 *              check. Under these conditions the function silently returns
 *              0 (success) on what is in fact a failure branch — the bug
 *              shape fixed by upstream commit 620b90d30c08 ("mtd: maps:
 *              fix error return code of physmap_flash_remove()").
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3/l0/error-return-code-missing
 * @tags reliability
 *       error-handling
 *       correctness
 */

import cpp

predicate errIsZeroAtFailureGoto(Function f, LocalVariable errVar, GotoStmt g) {
  f.fromSource() and
  errVar.getFunction() = f and
  errVar.getName() = "err" and
  errVar.getType().getUnspecifiedType() instanceof IntType and
  errVar.getInitializer().getExpr().getValue() = "0" and
  exists(ReturnStmt rs |
    rs.getEnclosingFunction() = f and
    rs.getExpr().(VariableAccess).getTarget() = errVar
  ) and
  g.getEnclosingFunction() = f and
  exists(IfStmt ifs |
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
  )
}

from Function f, LocalVariable errVar, GotoStmt g
where errIsZeroAtFailureGoto(f, errVar, g)
select g,
       "Function `" + f.getName() +
       "` jumps to cleanup with `err` still 0 on a failure branch — " +
       "caller will see success."
