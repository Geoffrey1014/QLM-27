/**
 * @name Missing error-code assignment before goto-cleanup on allocation failure
 * @description Detects a NULL-check on the result of an allocation/acquire-style
 *              function whose then-branch transfers control to a cleanup label
 *              via `goto`, without assigning a negative errno to the function's
 *              status/return variable. This is the bug class fixed by commit
 *              c021e0235770 (usb: gadget: legacy: fix error return code of
 *              multi_bind): `usb_desc = usb_otg_descriptor_alloc(gadget); if
 *              (!usb_desc) goto fail_string_ids;` leaves `status` at 0 so the
 *              function returns success on an allocation failure.
 * @kind problem
 * @problem.severity warning
 * @id cpp/missing-error-code-before-goto-cleanup
 * @tags correctness
 *       error-handling
 */

import cpp

/**
 * A function call whose return value is conventionally an allocated/acquired
 * resource that callers must NULL-check.  We approximate the family with name
 * heuristics that match kernel allocator / acquire APIs.
 */
predicate isAllocLikeCall(FunctionCall fc) {
  exists(string n | n = fc.getTarget().getName() |
    n.matches("%alloc%") or
    n.matches("%_create%") or
    n.matches("%_get") or
    n.matches("%_get_%") or
    n.matches("kmalloc%") or
    n.matches("kzalloc%") or
    n.matches("kcalloc%") or
    n.matches("vmalloc%") or
    n.matches("vzalloc%") or
    n.matches("devm_kzalloc%") or
    n.matches("devm_kmalloc%") or
    n.matches("kmemdup%") or
    n.matches("kstrdup%") or
    n.matches("dma_alloc_%") or
    n.matches("of_%") or
    n.matches("ioremap%")
  )
}

/**
 * A goto statement that transfers control to a label whose name suggests an
 * error/cleanup target (fail, err, out, cleanup, undo, ...).
 */
predicate isErrorGoto(GotoStmt g) {
  exists(string lname | lname = g.getName().toLowerCase() |
    lname.matches("fail%") or
    lname.matches("err%") or
    lname.matches("out%") or
    lname.matches("cleanup%") or
    lname.matches("undo%") or
    lname.matches("free%") or
    lname.matches("release%") or
    lname.matches("abort%") or
    lname.matches("bad%")
  )
}

/**
 * Holds if `s` is reachable from `start` by walking into block bodies and
 * if/else children, without re-entering loops.  We use this to look for
 * an assignment of an error code to `errVar` between the NULL-check and the
 * goto.  We bound the depth implicitly by the AST.
 */
predicate containsAssignToErrVar(Stmt s, Variable errVar) {
  exists(AssignExpr a | a.getEnclosingStmt() = s and a.getLValue().(VariableAccess).getTarget() = errVar)
  or
  exists(Stmt child | child.getParentStmt() = s and containsAssignToErrVar(child, errVar))
}

/**
 * A candidate error-status variable: a local variable of integer type whose
 * name strongly suggests it is the function's return-code holder
 * (status, ret, rc, err, error, result).
 */
predicate isErrorStatusVar(LocalVariable v) {
  v.getType().getUnspecifiedType() instanceof IntegralType and
  exists(string n | n = v.getName().toLowerCase() |
    n = "status" or n = "ret" or n = "rc" or n = "err" or
    n = "error" or n = "result" or n = "retval" or n = "rv"
  )
}

/**
 * The function `f` has a local `errVar` that is returned at the end (i.e. it
 * actually is the return-code variable).
 */
predicate isReturnedErrVar(Function f, LocalVariable errVar) {
  isErrorStatusVar(errVar) and
  errVar.getFunction() = f and
  exists(ReturnStmt r | r.getEnclosingFunction() = f and
    r.getExpr().(VariableAccess).getTarget() = errVar)
}

from
  Function f, LocalVariable errVar, IfStmt ifs, FunctionCall alloc,
  VariableAccess nullCheck, GotoStmt g, BlockStmt thenBlock
where
  // The function has a return-code variable that it eventually returns.
  isReturnedErrVar(f, errVar) and
  // An allocation-like call inside f.
  alloc.getEnclosingFunction() = f and
  isAllocLikeCall(alloc) and
  // The if's condition tests the result of `alloc` for NULL.
  ifs.getEnclosingFunction() = f and
  (
    // if (!x)
    exists(NotExpr ne, VariableAccess va |
      ne = ifs.getCondition() and va = ne.getOperand() and
      va.getTarget() instanceof LocalVariable and
      exists(AssignExpr ae |
        ae.getLValue().(VariableAccess).getTarget() = va.getTarget() and
        ae.getRValue() = alloc
      ) and nullCheck = va
    )
    or
    // if (x == NULL)
    exists(EQExpr eq, VariableAccess va |
      eq = ifs.getCondition() and va = eq.getAnOperand() and
      eq.getAnOperand() instanceof Literal and
      va.getTarget() instanceof LocalVariable and
      exists(AssignExpr ae |
        ae.getLValue().(VariableAccess).getTarget() = va.getTarget() and
        ae.getRValue() = alloc
      ) and nullCheck = va
    )
  ) and
  // The then-branch contains a goto to an error/cleanup label.
  (
    (thenBlock = ifs.getThen() and g.getParentStmt+() = thenBlock)
    or
    g = ifs.getThen()
  ) and
  isErrorGoto(g) and
  // The then-branch does NOT assign to errVar before the goto.
  (
    if exists(BlockStmt bb | bb = ifs.getThen())
    then not containsAssignToErrVar(ifs.getThen(), errVar)
    else not exists(AssignExpr ae |
      ae.getEnclosingStmt() = ifs.getThen() and
      ae.getLValue().(VariableAccess).getTarget() = errVar
    )
  )
select ifs,
  "Allocation failure handler gotos error label '" + g.getName() +
    "' without assigning an error code to '" + errVar.getName() +
    "'; the function may return success on failure."
