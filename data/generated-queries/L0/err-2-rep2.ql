/**
 * @name Function returns success on a failure-branch goto without
 *       setting the returned `ret` variable
 *       (error-return-code pattern) [L0 zero-shot single-predicate]
 * @description Detects int-returning functions where:
 *                P1. a local `int ret;` flows to the return value
 *                    (helper predicate isRetReturnFunction); and
 *              (inlined in the assembly where-clause because L0
 *               limits us to a single predicate):
 *                P2. an IfStmt's then-branch contains a `goto <cleanup>`
 *                    targeting that return path;
 *                P3. the if-condition does not read `ret` itself, and
 *                    nothing earlier in the then-block assigns a value
 *                    to `ret` before the goto.
 *              Under these conditions the function silently returns
 *              whatever `ret` last held (typically 0 = success) on
 *              what is in fact a failure branch — the bug shape fixed
 *              by upstream commit 45c7eaeb29d6 ("thermal: thermal_of:
 *              Fix error return code of thermal_of_populate_bind_params()").
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3/l0/error-return-code-missing-ret
 * @tags reliability
 *       error-handling
 *       error-return
 */

import cpp

/* P1 — function has `int ret;` whose value reaches a return. */
predicate isRetReturnFunction(Function f, LocalVariable retVar) {
  f.fromSource() and
  retVar.getFunction() = f and
  retVar.getName() = "ret" and
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
        a.getLValue().(VariableAccess).getTarget() = retVar
      )
    )
  )
select g,
       "Function `" + f.getName() +
       "` reaches its cleanup goto without setting `ret` on a failure branch — " +
       "caller may see success."
