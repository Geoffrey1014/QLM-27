/**
 * @name  rq3-c2-err-3-rep1
 * @id    cpp/rq3/c2/err-3-rep1
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2 (error-return omission).
 */
import cpp

/* The function has a local "ret" variable used as the error return. */
predicate has_ret_local(Function f, LocalVariable ret) {
  ret.getFunction() = f and
  ret.getName() = "ret" and
  ret.getType().getUnspecifiedType() instanceof IntegralType
}

/* The function returns the value of "ret" at one of its return statements. */
predicate returns_ret(Function f, LocalVariable ret) {
  has_ret_local(f, ret) and
  exists(ReturnStmt rs, VariableAccess va |
    rs.getEnclosingFunction() = f and
    va = rs.getExpr() and
    va.getTarget() = ret
  )
}

/* "ret" is initialised to 0 (success) at declaration. */
predicate ret_inited_zero(LocalVariable ret) {
  exists(Expr init | init = ret.getInitializer().getExpr() and init.getValue() = "0")
}

/* An if-statement whose condition tests "!expr" (a null/zero check on a pointer-like). */
predicate is_null_check_if(IfStmt ifs, Expr checked) {
  exists(NotExpr ne |
    ne = ifs.getCondition() and
    checked = ne.getOperand()
  )
}

/* The then-branch of "ifs" contains a goto-statement and does NOT assign "ret". */
predicate then_gotos_without_assigning_ret(IfStmt ifs, LocalVariable ret, GotoStmt g) {
  g.getParent*() = ifs.getThen() and
  not exists(AssignExpr ae |
    ae.getParent*() = ifs.getThen() and
    ae.getLValue().(VariableAccess).getTarget() = ret
  )
}

/* The goto's target label is followed (control-flow wise) by "return ret;". */
predicate goto_target_returns_ret(GotoStmt g, LocalVariable ret) {
  exists(ReturnStmt rs, VariableAccess va |
    rs.getEnclosingFunction() = g.getEnclosingFunction() and
    va = rs.getExpr() and
    va.getTarget() = ret and
    /* the label is in the same function and the return uses ret */
    g.getTarget().getEnclosingFunction() = g.getEnclosingFunction()
  )
}

from Function f, LocalVariable ret, IfStmt ifs, GotoStmt g, Expr checked
where
  has_ret_local(f, ret) and
  returns_ret(f, ret) and
  ret_inited_zero(ret) and
  ifs.getEnclosingFunction() = f and
  is_null_check_if(ifs, checked) and
  then_gotos_without_assigning_ret(ifs, ret, g) and
  goto_target_returns_ret(g, ret)
select ifs,
  "Error path in '" + f.getName() +
  "' goes to cleanup via goto without assigning an error code to 'ret'."
