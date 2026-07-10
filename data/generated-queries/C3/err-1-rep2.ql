/**
 * @name Function returns success (0) on a failure-branch goto
 *       (error-return-code pattern)
 * @description Detects int-returning functions where:
 *                P1. a local `int err = 0;` flows to the return value;
 *                P2. an IfStmt's then-branch contains a `goto cleanup`
 *                    targeting that return path; and
 *                P3. the if-condition does not read `err` itself, and
 *                    nothing in the then-branch assigns a non-zero value
 *                    to `err` before the goto.
 *              Under these conditions the function silently returns 0
 *              (success) on what is in fact a failure branch — the bug
 *              shape fixed by upstream commit 620b90d30c08 ("mtd: maps:
 *              fix error return code of physmap_flash_remove()").
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3/c3/error-return-code-missing
 * @tags reliability
 *       error-handling
 *       correctness
 */

import cpp

/* P1 — function has `int err = 0;` whose value reaches a return. */
predicate isErrReturnFunction(Function f, LocalVariable errVar) {
  f.fromSource() and
  errVar.getFunction() = f and
  errVar.getName() = "err" and
  errVar.getType().getUnspecifiedType() instanceof IntType and
  exists(ReturnStmt rs |
    rs.getEnclosingFunction() = f and
    rs.getExpr().(VariableAccess).getTarget() = errVar
  ) and
  errVar.getInitializer().getExpr().getValue() = "0"
}

/* P2 — goto sitting in the then-branch of an IfStmt (a failure shortcut). */
predicate isFailureBranchGoto(GotoStmt g, Function f) {
  g.getEnclosingFunction() = f and
  exists(IfStmt ifs |
    ifs.getThen() = g or
    ifs.getThen().(BlockStmt).getStmt(_) = g
  )
}

/* P3 — at this goto, `err` is still 0: the if-condition is not on err
 *      itself, and nothing earlier in the then-block assigned a non-zero
 *      value to err. */
predicate errIsZeroAtGoto(GotoStmt g, LocalVariable errVar) {
  errVar.getName() = "err" and
  errVar.getFunction() = g.getEnclosingFunction() and
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
where
  isErrReturnFunction(f, errVar) and
  g.getEnclosingFunction() = f and
  isFailureBranchGoto(g, f) and
  errIsZeroAtGoto(g, errVar)
select g,
       "Function `" + f.getName() +
       "` reaches its cleanup goto with `err` still 0 on a failure branch — " +
       "caller will see success."
