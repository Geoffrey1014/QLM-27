/**
 * @name  rq3-c2-err-3-rep3
 * @id    cpp/rq3/c2/err-3-rep3
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects error-return code omission: an error branch that
 *              gotos a cleanup label without first assigning a negative
 *              errno to the function's return-code variable.
 */
import cpp

/** Holds if `e` denotes a negative errno constant (e.g. -ENOENT, -EINVAL, or any negative integer literal). */
predicate isNegativeErrnoExpr(Expr e) {
  exists(int v | e.getValue().toInt() = v and v < 0)
  or
  exists(UnaryMinusExpr um | um = e and um.getOperand() instanceof Literal)
  or
  // Accept casts around the above
  isNegativeErrnoExpr(e.(Conversion).getExpr())
}

/** Holds if `v` is the local variable that holds the return code of function `f`:
 *  it is an `int` declared in `f`, and some `return` statement in `f` returns it
 *  (possibly via a conversion). */
predicate isReturnCodeVar(LocalVariable v, Function f) {
  v.getFunction() = f and
  v.getType().getUnspecifiedType() instanceof IntType and
  exists(ReturnStmt r, VariableAccess va |
    r.getEnclosingFunction() = f and
    va = r.getExpr().getAChild*() and
    va.getTarget() = v
  )
}

/** Holds if statement `s` contains, directly or transitively, an assignment
 *  of a negative errno value to `v`. */
predicate assignsErrnoTo(Stmt s, LocalVariable v) {
  exists(AssignExpr ae |
    ae.getEnclosingStmt() = s.getAChild*() and
    ae.getLValue().(VariableAccess).getTarget() = v and
    isNegativeErrnoExpr(ae.getRValue())
  )
}

/** Holds if `g` is a goto inside the then-branch of `ifs`, jumping forward to
 *  a labelled "cleanup-ish" statement (any label) inside the same function. */
predicate errorBranchGoto(IfStmt ifs, GotoStmt g) {
  g.getParent+() = ifs.getThen() and
  exists(Stmt target | target = g.getTarget() and
    target.getEnclosingFunction() = ifs.getEnclosingFunction())
}

/** Holds if the then-branch of `ifs` reaches the goto `g` without first
 *  assigning a negative errno to `ret`. */
predicate missingErrnoBeforeGoto(IfStmt ifs, GotoStmt g, LocalVariable ret) {
  errorBranchGoto(ifs, g) and
  not assignsErrnoTo(ifs.getThen(), ret)
}

from IfStmt ifs, GotoStmt g, LocalVariable ret, Function f
where
  f = ifs.getEnclosingFunction() and
  isReturnCodeVar(ret, f) and
  missingErrnoBeforeGoto(ifs, g, ret)
select ifs, "Error branch gotos cleanup label without assigning a negative errno to return-code variable '" + ret.getName() + "'."
