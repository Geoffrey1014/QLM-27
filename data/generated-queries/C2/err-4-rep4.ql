/**
 * @name  rq3-c2-err-4-rep4
 * @id    cpp/rq3/c2/err-4-rep4
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects missing-error-code-assignment on a NULL-check failure
 *              branch that gotos a shared cleanup label, while the enclosing
 *              function returns an int status that was not updated.
 */

import cpp

/** A call whose return type is a pointer and whose result is assigned to a local variable. */
predicate isAllocLikeCall(FunctionCall fc, Variable v) {
  fc.getType() instanceof PointerType and
  exists(AssignExpr ae |
    ae.getRValue() = fc and
    ae.getLValue() = v.getAnAccess()
  )
}

/** `if (!v)` or `if (v == NULL)` style null check on variable v. */
predicate isNullCheckOf(IfStmt ifs, Variable v) {
  exists(Expr cond | cond = ifs.getCondition() |
    cond.(NotExpr).getOperand() = v.getAnAccess()
    or
    exists(EQExpr eq |
      eq = cond and
      eq.getAnOperand() = v.getAnAccess() and
      eq.getAnOperand().getValue() = "0"
    )
  )
}

/** The "then" branch of `ifs` contains a goto-statement `g`. */
predicate nullBranchHasGoto(IfStmt ifs, GotoStmt g) {
  g.getParentStmt*() = ifs.getThen()
}

/** Statement `s` assigns an integer constant (typically a negative errno) to variable `status`. */
predicate assignsIntConstantTo(Stmt s, Variable status) {
  exists(ExprStmt es, AssignExpr ae |
    es = s and
    ae = es.getExpr() and
    ae.getLValue() = status.getAnAccess() and
    ae.getRValue() instanceof Literal
  )
  or
  exists(ExprStmt es, AssignExpr ae, UnaryMinusExpr um |
    es = s and
    ae = es.getExpr() and
    ae.getLValue() = status.getAnAccess() and
    ae.getRValue() = um and
    um.getOperand() instanceof Literal
  )
}

/** Variable `status` is an int-typed local of `f` that is returned by some ReturnStmt. */
predicate isReturnedStatusVar(Function f, Variable status) {
  status.(LocalVariable).getFunction() = f and
  status.getType().getUnspecifiedType() instanceof IntType and
  exists(ReturnStmt rs |
    rs.getEnclosingFunction() = f and
    rs.getExpr() = status.getAnAccess()
  )
}

/**
 * Core: in function `f`, an alloc-like call assigns to local pointer `v`;
 * an `if (!v)` then-branch does `goto g`, but no assignment to the returned
 * status variable `status` occurs inside that then-branch before the goto.
 */
predicate missingErrorAssignBeforeGoto(
  Function f, FunctionCall alloc, Variable v, IfStmt ifs, GotoStmt g, Variable status
) {
  isAllocLikeCall(alloc, v) and
  alloc.getEnclosingFunction() = f and
  isNullCheckOf(ifs, v) and
  ifs.getEnclosingFunction() = f and
  nullBranchHasGoto(ifs, g) and
  isReturnedStatusVar(f, status) and
  status != v and
  not exists(Stmt s |
    s.getParentStmt*() = ifs.getThen() and
    assignsIntConstantTo(s, status)
  )
}

from Function f, FunctionCall alloc, Variable v, IfStmt ifs, GotoStmt g, Variable status
where missingErrorAssignBeforeGoto(f, alloc, v, ifs, g, status)
select alloc,
  "Missing error code assignment to '" + status.getName() +
    "' on NULL-check failure path of '" + alloc.getTarget().getName() +
    "' before goto '" + g.getName() + "' in function '" + f.getName() + "'."
