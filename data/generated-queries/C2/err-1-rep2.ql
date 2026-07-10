/**
 * @name  rq3-c2-err-1-rep2
 * @id    cpp/rq3/c2/err-1-rep2
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detect functions that have an err return variable initialized
 *              to 0, contain a NULL-check on a call result that gotos a
 *              shared cleanup label without assigning err, causing the
 *              function to silently return success on a failure path.
 */

import cpp

/**
 * f returns int and has a local variable `err` that is initialized to 0 and
 * eventually returned (the error-code holder pattern).
 */
predicate hasErrReturnHolder(Function f, LocalVariable err) {
  f.getType().getUnspecifiedType() instanceof IntType and
  err.getFunction() = f and
  err.getName() = "err" and
  err.getType().getUnspecifiedType() instanceof IntType and
  exists(Expr init | init = err.getInitializer().getExpr() | init.getValue() = "0") and
  exists(ReturnStmt rs |
    rs.getEnclosingFunction() = f and
    rs.getExpr().(VariableAccess).getTarget() = err
  )
}

/**
 * `ifs` is a null-check `if (!call(...))` (or `if (call(...) == NULL)` style)
 * whose then-branch contains a goto to a cleanup label.
 */
predicate nullCheckGotoesCleanup(IfStmt ifs, GotoStmt gs, FunctionCall fc) {
  ifs.getThen().(BlockStmt).getAStmt() = gs
  or
  ifs.getThen() = gs
  or
  // Allow if-then to be a single stmt that itself is the goto
  ifs.getThen().getAChild*() = gs
  and
  exists(Expr cond | cond = ifs.getCondition() |
    // pattern: if (!X)
    cond.(NotExpr).getOperand().(VariableAccess).getTarget() =
      fc.getEnclosingStmt().(DeclStmt).getADeclaration()
    or
    // pattern: if (!X) where X holds the call result via prior assignment
    exists(VariableAccess va |
      va = cond.(NotExpr).getOperand() and
      fc.getParent+() = ifs.getEnclosingFunction().getBlock()
    )
  )
}

/**
 * Within the body of `ifs` (which gotos `gs`), the variable `err` is NOT
 * assigned before the goto. I.e. control reaches the goto with err unchanged.
 */
predicate errNotAssignedBeforeGoto(IfStmt ifs, GotoStmt gs, LocalVariable err) {
  ifs.getThen().getAChild*() = gs and
  not exists(AssignExpr ae |
    ae.getEnclosingStmt().getParent*() = ifs.getThen() and
    ae.getLValue().(VariableAccess).getTarget() = err
  )
}

/**
 * The goto target label is shared cleanup: at least one other statement in
 * the same function also branches to the same label, and reaching the label
 * leads to `return err;`.
 */
predicate gotoTargetIsSharedCleanup(GotoStmt gs) {
  exists(Function f | f = gs.getEnclosingFunction() |
    exists(GotoStmt other |
      other != gs and
      other.getEnclosingFunction() = f and
      other.getTarget() = gs.getTarget()
    )
    and
    exists(ReturnStmt rs |
      rs.getEnclosingFunction() = f and
      rs.getExpr() instanceof VariableAccess
    )
  )
}

from Function f, LocalVariable err, IfStmt ifs, GotoStmt gs, FunctionCall fc
where
  hasErrReturnHolder(f, err) and
  ifs.getEnclosingFunction() = f and
  gs.getEnclosingFunction() = f and
  nullCheckGotoesCleanup(ifs, gs, fc) and
  errNotAssignedBeforeGoto(ifs, gs, err) and
  gotoTargetIsSharedCleanup(gs)
select ifs,
  "Error-return-code bug: NULL-check branch gotoes shared cleanup label '" +
    gs.getName() + "' without assigning the function's err variable; " +
    "function will silently return 0 (success) on this failure path."
