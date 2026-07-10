/**
 * @name  rq3-c2-err-4-rep3
 * @id    cpp/rq3/c2/err-4-rep3
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects: pointer-returning allocator's NULL check jumps to a
 *              cleanup label without first assigning a negative error code
 *              to the function's status/ret return variable.
 */
import cpp

/** A function whose name suggests it allocates and returns a pointer. */
predicate isAllocFunction(Function f) {
  f.getType().getUnspecifiedType() instanceof PointerType and
  (
    f.getName().toLowerCase().matches("%alloc%") or
    f.getName().toLowerCase().matches("%create%") or
    f.getName().toLowerCase().matches("%new%") or
    f.getName().toLowerCase().matches("%dup%") or
    f.getName().toLowerCase().matches("%kmemdup%")
  )
}

/** A call to an alloc function whose result is assigned to a local variable. */
predicate allocAssignment(FunctionCall fc, LocalVariable lv) {
  isAllocFunction(fc.getTarget()) and
  exists(AssignExpr ae |
    ae.getRValue() = fc and
    ae.getLValue() = lv.getAnAccess()
  )
}

/** An `if (!v) goto L;` shape where v was assigned an alloc result. */
predicate nullCheckGoto(IfStmt ifs, LocalVariable lv, GotoStmt gs) {
  exists(FunctionCall fc | allocAssignment(fc, lv)) and
  (
    ifs.getCondition().(NotExpr).getOperand() = lv.getAnAccess() or
    exists(EQExpr eq |
      eq = ifs.getCondition() and
      eq.getAnOperand() = lv.getAnAccess() and
      eq.getAnOperand().getValue() = "0"
    )
  ) and
  gs = ifs.getThen().(GotoStmt)
}

/** Look for a "status/ret/err" int variable in the enclosing function. */
predicate hasStatusVariable(Function f, LocalVariable status) {
  status.getFunction() = f and
  status.getType().getUnspecifiedType() instanceof IntegralType and
  (
    status.getName() = "status" or
    status.getName() = "ret" or
    status.getName() = "rc" or
    status.getName() = "err" or
    status.getName() = "error" or
    status.getName() = "retval"
  )
}

/** The goto's basic-block predecessor does NOT assign a negative literal to status. */
predicate gotoWithoutErrorAssign(GotoStmt gs, LocalVariable status) {
  hasStatusVariable(gs.getEnclosingFunction(), status) and
  not exists(AssignExpr ae |
    ae.getLValue() = status.getAnAccess() and
    ae.getEnclosingFunction() = gs.getEnclosingFunction() and
    ae.getLocation().getStartLine() < gs.getLocation().getStartLine() and
    ae.getLocation().getStartLine() >= gs.getLocation().getStartLine() - 5 and
    (
      ae.getRValue().getValue().regexpMatch("-[0-9]+") or
      ae.getRValue() instanceof UnaryMinusExpr
    )
  )
}

from IfStmt ifs, LocalVariable lv, GotoStmt gs, LocalVariable status, FunctionCall fc
where
  allocAssignment(fc, lv) and
  nullCheckGoto(ifs, lv, gs) and
  gotoWithoutErrorAssign(gs, status) and
  gs.getEnclosingFunction() = fc.getEnclosingFunction()
select ifs,
  "Possible missing error-return: alloc result " + lv.getName() +
    " null-checked and goto label" +
    " without setting " + status.getName() + " to a negative error code."
