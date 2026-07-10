/**
 * @name Function returns stale/success value on a failure-branch goto
 *       (error-return-code pattern) [L0 zero-shot single-predicate]
 * @description Detects int-returning functions where:
 *                P1. a local int `status` (or `err`/`ret`/`rc`) flows to
 *                    the function's return value
 *                    (helper predicate isStatusReturnFunction); and
 *              (inlined in the assembly where-clause because L0 limits us
 *               to a single predicate):
 *                P2. an IfStmt's then-branch contains a `goto cleanup`
 *                    targeting that return path;
 *                P3. the if-condition does not read the return variable
 *                    itself, and nothing earlier in the then-block assigns
 *                    a value to that variable before the goto.
 *              Under these conditions the function silently returns
 *              whatever value the return variable held (typically 0 —
 *              success) on what is in fact a failure branch — the bug
 *              shape fixed by upstream commit c021e0235770 ("usb: gadget:
 *              legacy: fix error return code of multi_bind()").
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3/l0/error-return-code-missing
 * @tags reliability
 *       error-handling
 *       error-return
 */

import cpp

/* P1 — function has an int-typed local (status/err/ret/rc) that reaches a return. */
predicate isStatusReturnFunction(Function f, LocalVariable statusVar) {
  f.fromSource() and
  statusVar.getFunction() = f and
  (statusVar.getName() = "status" or
   statusVar.getName() = "err" or
   statusVar.getName() = "ret" or
   statusVar.getName() = "rc") and
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
       "` reaches its cleanup goto without assigning the return variable `" +
       statusVar.getName() + "` on a failure branch — caller may see stale/success value."
