/**
 * @name  rq3-c2-err-4-rep2
 * @id    cpp/rq3/c2/err-4-rep2
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detect error-handling paths where an allocation returns NULL,
 *              control flow gotos a cleanup/error label, but the status/return
 *              error code variable is never set on that path.
 */

import cpp

/** A local pointer variable assigned from a call whose name suggests allocation. */
predicate alloc_assignment(LocalVariable ptr, FunctionCall alloc, ExprStmt assignStmt) {
  exists(AssignExpr ae |
    ae = assignStmt.getExpr() and
    ae.getLValue() = ptr.getAnAccess() and
    ae.getRValue() = alloc and
    (
      alloc.getTarget().getName().toLowerCase().matches("%alloc%") or
      alloc.getTarget().getName().toLowerCase().matches("%_new%") or
      alloc.getTarget().getName().toLowerCase().matches("kmalloc%") or
      alloc.getTarget().getName().toLowerCase().matches("kzalloc%") or
      alloc.getTarget().getName().toLowerCase().matches("%dup%")
    )
  )
}

/** An `if (!ptr)` guard whose condition tests the allocation result for null. */
predicate null_check_guard(LocalVariable ptr, IfStmt ifs) {
  exists(NotExpr ne |
    ne = ifs.getCondition() and
    ne.getOperand() = ptr.getAnAccess()
  )
  or
  exists(EQExpr eq |
    eq = ifs.getCondition() and
    eq.getAnOperand() = ptr.getAnAccess() and
    eq.getAnOperand().getValue() = "0"
  )
}

/** A goto statement inside the then-branch of the null-check guard. */
predicate goto_inside_null_branch(IfStmt ifs, GotoStmt gs) {
  gs.getParentStmt*() = ifs.getThen()
}

/** A status / err / ret local variable in the same function. */
predicate status_like_variable(LocalVariable status, Function f) {
  status.getFunction() = f and
  (
    status.getName().toLowerCase() = "status" or
    status.getName().toLowerCase() = "ret" or
    status.getName().toLowerCase() = "err" or
    status.getName().toLowerCase() = "rc" or
    status.getName().toLowerCase() = "error"
  ) and
  status.getType().getUnspecifiedType() instanceof IntegralType
}

/** The status variable is assigned a (negative or non-zero) value within the
 *  then-branch of the null-check guard, before the goto. */
predicate status_assigned_in_branch(LocalVariable status, IfStmt ifs) {
  exists(AssignExpr ae |
    ae.getLValue() = status.getAnAccess() and
    ae.getEnclosingStmt().getParentStmt*() = ifs.getThen()
  )
}

/** The null-check / goto path fails to set the status variable. */
predicate missing_status_set(
  Function f, LocalVariable ptr, IfStmt ifs, GotoStmt gs, LocalVariable status
) {
  exists(FunctionCall alloc, ExprStmt assignStmt |
    alloc_assignment(ptr, alloc, assignStmt) and
    alloc.getEnclosingFunction() = f and
    ifs.getEnclosingFunction() = f and
    null_check_guard(ptr, ifs) and
    goto_inside_null_branch(ifs, gs) and
    status_like_variable(status, f) and
    not status_assigned_in_branch(status, ifs)
  )
}

from Function f, LocalVariable ptr, IfStmt ifs, GotoStmt gs, LocalVariable status
where missing_status_set(f, ptr, ifs, gs, status)
select ifs,
  "Allocation '" + ptr.getName() +
    "' null-check gotos '" + gs.getName() +
    "' without setting status variable '" + status.getName() + "'."
