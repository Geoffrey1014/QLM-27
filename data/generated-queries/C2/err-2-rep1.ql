/**
 * @name  rq3-c2-err-2-rep1
 * @id    cpp/rq3/c2/err-2-rep1
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects functions where an error-path `goto cleanup` is taken
 *              without first assigning a negative errno to the return variable,
 *              causing the function to return success (0) on a real failure.
 */
import cpp

/* Predicate 1: function returns the value of a local variable (the "ret" variable). */
predicate returnsLocalVar(Function f, LocalVariable ret) {
  exists(ReturnStmt rs, VariableAccess va |
    rs.getEnclosingFunction() = f and
    rs.getExpr() = va and
    va.getTarget() = ret and
    ret.getType().getUnspecifiedType() instanceof IntegralType
  )
}

/* Predicate 2: ret is initialized to 0 (so default value would be success). */
predicate retDefaultsToZero(LocalVariable ret) {
  ret.getInitializer().getExpr().getValue() = "0"
  or
  not exists(ret.getInitializer())
}

/* Predicate 3: a goto statement targets a cleanup label inside function f. */
predicate cleanupGoto(Function f, GotoStmt gs) {
  gs.getEnclosingFunction() = f and
  exists(string lbl | lbl = gs.getName() |
    lbl.toLowerCase().matches("%end%") or
    lbl.toLowerCase().matches("%err%") or
    lbl.toLowerCase().matches("%fail%") or
    lbl.toLowerCase().matches("%out%") or
    lbl.toLowerCase().matches("%free%") or
    lbl.toLowerCase().matches("%cleanup%") or
    lbl.toLowerCase().matches("%unlock%")
  )
}

/* Predicate 4: the goto is inside an `if` whose condition looks like an
 * error/failure test (e.g. `!x`, `x == NULL`, `x < 0`, `!count`). */
predicate gotoInErrorBranch(GotoStmt gs) {
  exists(IfStmt ifs, Expr cond |
    ifs.getCondition() = cond and
    gs.getParentStmt*() = ifs.getThen() and
    (
      cond instanceof NotExpr
      or
      cond.(EQExpr).getAnOperand() instanceof Literal
      or
      cond instanceof LTExpr
      or
      cond instanceof LEExpr
      or
      cond instanceof GTExpr
      or
      cond instanceof GEExpr
    )
  )
}

/* Predicate 5: on the path leading to gs there is no assignment to `ret`
 * within the same enclosing if-then block. */
predicate retNotAssignedBeforeGoto(GotoStmt gs, LocalVariable ret) {
  exists(IfStmt ifs |
    gs.getParentStmt*() = ifs.getThen() and
    not exists(Assignment a |
      a.getLValue().(VariableAccess).getTarget() = ret and
      a.getEnclosingStmt().getParentStmt*() = ifs.getThen()
    )
  )
}

from Function f, LocalVariable ret, GotoStmt gs
where
  returnsLocalVar(f, ret) and
  retDefaultsToZero(ret) and
  cleanupGoto(f, gs) and
  gotoInErrorBranch(gs) and
  retNotAssignedBeforeGoto(gs, ret) and
  ret.getFunction() = f
select gs, "Goto to cleanup label '" + gs.getName() +
  "' on error path may return success (variable '" + ret.getName() + "' not assigned an error code)."
