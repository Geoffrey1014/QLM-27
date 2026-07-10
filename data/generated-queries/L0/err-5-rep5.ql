/**
 * @name Function returns success (0) on a failure-branch goto
 *       (error-return-code pattern) [L0 zero-shot single-predicate]
 * @description Detects int-returning functions where:
 *                P1. a local `int ret/err = 0;` flows to the return value
 *                    (helper predicate isErrReturnFunction); and
 *              (inlined in the assembly where-clause because L0
 *               limits us to a single predicate):
 *                P2. an IfStmt's then-branch contains a `goto <label>`
 *                    targeting a cleanup tail that ultimately returns the
 *                    same variable;
 *                P3. the if-condition does not read `ret`/`err` itself, and
 *                    nothing earlier in the then-block assigns a non-zero
 *                    value to the return variable before the goto.
 *              Under these conditions the function silently returns 0
 *              (success) on what is in fact a failure branch — the bug
 *              shape fixed by upstream commit 31d82c2c787d ("kernel:
 *              kexec_file: fix error return code of
 *              kexec_calculate_store_digests()").
 * @kind problem
 * @problem.severity warning
 * @id qlm-rq3-l0-error-return-code-missing
 * @tags reliability
 *       error-handling
 *       error-return
 */

import cpp

/* P1 — function has `int ret/err/rc/error = 0;` whose value reaches a return. */
predicate isErrReturnFunction(Function f, LocalVariable errVar) {
  f.fromSource() and
  errVar.getFunction() = f and
  (errVar.getName() = "ret" or
   errVar.getName() = "err" or
   errVar.getName() = "rc"  or
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
        a.getLValue().(VariableAccess).getTarget() = errVar and
        a.getRValue().getValue() != "0"
      )
    )
  )
select g,
       "Function `" + f.getName() +
       "` reaches its cleanup goto with `" + errVar.getName() +
       "` still 0 on a failure branch — caller will see success."
