/**
 * @name Error-return-code missing on failure goto (error-return pattern) [L0]
 * @description Detects int-returning functions with a local `err = 0`
 *              initializer whose failure-branch `goto <cleanup>` does NOT
 *              first assign a non-zero value to `err`, so the function
 *              silently returns 0 on an error path. Pattern from commit
 *              620b90d30c08 ("mtd: maps: fix error return code of
 *              physmap_flash_remove()"). CWE-394.
 *
 *              L0 zero-shot compositional variant: only one helper
 *              predicate is defined (isErrReturnFunction). The
 *              missing-assignment / failure-branch-goto tests are inlined
 *              in the from-where-select clause per L0 N_PRED=1 rule.
 * @kind problem
 * @problem.severity warning
 * @id qlm/rq3/l0/error-return-missing-code
 * @tags reliability
 *       error-return
 *       correctness
 */

import cpp

predicate isErrReturnFunction(Function f, LocalVariable errVar) {
  f.fromSource() and
  errVar.getFunction() = f and
  errVar.getName() = "err" and
  errVar.getType().getUnspecifiedType() instanceof IntType and
  errVar.getInitializer().getExpr().getValue() = "0" and
  exists(ReturnStmt rs |
    rs.getEnclosingFunction() = f and
    rs.getExpr().(VariableAccess).getTarget() = errVar
  )
}

from Function f, LocalVariable errVar, IfStmt ifs, GotoStmt g
where
  isErrReturnFunction(f, errVar) and
  ifs.getEnclosingFunction() = f and
  g.getEnclosingFunction() = f and
  // goto sits inside the then-branch of the if
  g.getParent+() = ifs.getThen() and
  // and no assignment to errVar appears anywhere inside that then-branch
  not exists(Assignment a |
    a.getEnclosingFunction() = f and
    a.getLValue().(VariableAccess).getTarget() = errVar and
    a.getParent+() = ifs.getThen()
  )
select g,
       "error-return-code bug in " + f.getName() +
       ": failure-branch goto without assigning non-zero to '" +
       errVar.getName() + "' first (CWE-394)."
