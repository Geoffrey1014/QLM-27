/**
 * @name error-return-code: goto to cleanup label without assigning -errno
 * @description Detects an if-branch that goto's a cleanup label without first
 *              assigning a negative errno to the variable the enclosing
 *              function returns. Modeled after
 *              45c7eaeb29d6 ("thermal: thermal_of: Fix error return code of
 *              thermal_of_populate_bind_params()").
 * @kind problem
 * @problem.severity warning
 * @id qlm/error-return-code-goto-l0-err2
 * @tags correctness
 */

import cpp

predicate gotoWithoutErrorAssign(IfStmt ifs, GotoStmt g, Variable retVar) {
  // Goto sits inside the taken 'then' branch of `ifs`.
  ifs.getThen() = g.getEnclosingBlock*() and
  // retVar is a variable that is used as the value of some return statement
  // in the enclosing function (so it IS the function's error channel).
  exists(Function f, ReturnStmt r |
    f = ifs.getEnclosingFunction() and
    f = g.getEnclosingFunction() and
    r.getEnclosingFunction() = f and
    r.getExpr().(VariableAccess).getTarget() = retVar
  ) and
  // No assignment to retVar occurs anywhere inside the taken branch.
  not exists(AssignExpr ae |
    ae.getLValue().(VariableAccess).getTarget() = retVar and
    ae.getEnclosingStmt().getParentStmt*() = ifs.getThen()
  )
}

from Function f, IfStmt ifs, GotoStmt g, Variable retVar
where
  gotoWithoutErrorAssign(ifs, g, retVar) and
  f = ifs.getEnclosingFunction()
select g,
  "error-return-code bug: goto in " + f.getName() +
  "() leaves return variable '" + retVar.getName() +
  "' unset (no -errno assigned before jump)"
