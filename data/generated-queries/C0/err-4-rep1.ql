/**
 * @name Missing error code on allocation failure goto
 * @description When an allocator-like call returns NULL and the code branches via goto
 *              to an error-cleanup label without first assigning a negative errno to the
 *              status/ret/err variable that is returned at the cleanup label, the caller
 *              receives a stale (often zero / success) value despite the failure.
 *              Models the multi_bind() / usb_otg_descriptor_alloc() class of bug.
 * @kind problem
 * @problem.severity warning
 * @id cpp/missing-errno-on-alloc-null-goto
 * @tags correctness
 *       reliability
 *       error-handling
 */

import cpp
import semmle.code.cpp.controlflow.Guards

/**
 * A function whose name suggests it allocates / acquires a resource and may return NULL
 * on failure. Conservative: pointer return type and an "alloc"/"create"/"new"/"get"
 * naming hint, or known kernel allocators.
 */
predicate isAllocLikeFunction(Function f) {
  f.getType().getUnspecifiedType() instanceof PointerType and
  (
    f.getName().toLowerCase().matches("%alloc%") or
    f.getName().toLowerCase().matches("%_create%") or
    f.getName().toLowerCase().matches("create_%") or
    f.getName().toLowerCase().matches("%_new") or
    f.getName().toLowerCase().matches("kmalloc%") or
    f.getName().toLowerCase().matches("kzalloc%") or
    f.getName().toLowerCase().matches("kcalloc%") or
    f.getName().toLowerCase().matches("vmalloc%") or
    f.getName().toLowerCase().matches("devm_%alloc%") or
    f.getName() = "kmemdup" or
    f.getName() = "kstrdup"
  )
}

/** A local variable used as the error-return status of its enclosing function. */
predicate isStatusVar(LocalVariable v, Function enclosing) {
  v.getFunction() = enclosing and
  v.getType().getUnspecifiedType() instanceof IntegralType and
  (
    v.getName() = "status" or
    v.getName() = "ret" or
    v.getName() = "rc" or
    v.getName() = "err" or
    v.getName() = "error" or
    v.getName() = "result"
  ) and
  // The function must actually return that variable's value somewhere.
  exists(ReturnStmt rs, VariableAccess va |
    rs.getEnclosingFunction() = enclosing and
    va = rs.getExpr().(VariableAccess) and
    va.getTarget() = v
  )
}

/**
 * `gs` is an if-statement whose condition tests that the result of an alloc-like call
 * is NULL/zero, and whose then-branch transfers control via `goto` to a cleanup label.
 */
predicate nullCheckGotoCleanup(IfStmt gs, GotoStmt g, FunctionCall alloc) {
  isAllocLikeFunction(alloc.getTarget()) and
  // Condition references the alloc result (either directly or via a variable assigned
  // from the alloc on the immediately preceding statement).
  (
    gs.getCondition().getAChild*() = alloc
    or
    exists(LocalVariable lv, VariableAccess use, AssignExpr ae |
      ae.getRValue() = alloc and
      ae.getLValue().(VariableAccess).getTarget() = lv and
      use.getTarget() = lv and
      gs.getCondition().getAChild*() = use and
      // Condition shape: !lv  or  lv == 0/NULL
      (
        gs.getCondition() instanceof NotExpr or
        gs.getCondition().(EqualityOperation).getAnOperand().getValue() = "0"
      )
    )
  ) and
  g.getEnclosingStmt*() = gs.getThen() and
  exists(g.getTarget())
}

/**
 * Between the alloc call and the goto, no assignment of a negative literal (or call
 * returning errno) to `statusVar` occurs in the then-branch.
 */
predicate noErrnoAssignBeforeGoto(IfStmt gs, GotoStmt g, LocalVariable statusVar) {
  not exists(AssignExpr ae |
    ae.getEnclosingStmt().getParentStmt*() = gs.getThen() and
    ae.getLValue().(VariableAccess).getTarget() = statusVar and
    (
      // numeric negative literal e.g. -ENOMEM expands to a negative int
      ae.getRValue().getValue().regexpMatch("-[0-9]+")
      or
      // Macro use: assigning -SOMETHING (UnaryMinusExpr around a macro/enum access)
      ae.getRValue() instanceof UnaryMinusExpr
      or
      // Function call returning int (e.g. PTR_ERR(...) family)
      exists(FunctionCall fc | fc = ae.getRValue() |
        fc.getTarget().getName().toLowerCase().matches("%ptr_err%") or
        fc.getTarget().getName().toLowerCase().matches("%err_ptr%")
      )
    )
  )
}

/** The cleanup label returns `statusVar` without first reassigning it on this path. */
predicate cleanupReturnsStatus(GotoStmt g, LocalVariable statusVar) {
  exists(ReturnStmt rs |
    rs.getEnclosingFunction() = g.getEnclosingFunction() and
    rs.getExpr().(VariableAccess).getTarget() = statusVar
  )
}

from
  Function f, IfStmt gs, GotoStmt g, FunctionCall alloc, LocalVariable statusVar
where
  f = gs.getEnclosingFunction() and
  isStatusVar(statusVar, f) and
  nullCheckGotoCleanup(gs, g, alloc) and
  noErrnoAssignBeforeGoto(gs, g, statusVar) and
  cleanupReturnsStatus(g, statusVar) and
  // Exclude the trivial case where the alloc call itself was assigned into statusVar
  not exists(AssignExpr ae |
    ae.getRValue() = alloc and
    ae.getLValue().(VariableAccess).getTarget() = statusVar
  )
select gs,
  "Allocation '" + alloc.getTarget().getName() +
    "' may return NULL; control gotos cleanup label '" + g.getName() +
    "' without setting error code in '" + statusVar.getName() + "' (returned by " +
    f.getName() + ")."
