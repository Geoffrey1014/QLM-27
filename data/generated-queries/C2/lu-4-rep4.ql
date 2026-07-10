/**
 * @name  rq3-c2-lu-4-rep4
 * @id    cpp/rq3/c2/lu-4-rep4
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects missing platform_device_put on error paths after
 *              platform_device_alloc, modelled on commit 9bbfceea12a8
 *              (usb: dwc3: pci: prevent memory leak in dwc3_pci_probe).
 */

import cpp

/* Predicate 1: a call to the target acquisition API. */
predicate isTargetApiCall(FunctionCall fc) {
  fc.getTarget().getName() = "platform_device_alloc"
}

/* Predicate 2: a call to the cleanup post-operation that releases a
 * platform_device pointer, with arg being its first argument. */
predicate isPostOpCall(FunctionCall fc, Expr arg) {
  fc.getTarget().getName() = "platform_device_put" and
  arg = fc.getArgument(0)
}

/* Predicate 3: the variable (or field-access expression target) which
 * holds the result of the alloc.  We use the lvalue assigned from the
 * alloc call. */
predicate holdsAllocResult(Expr holder, FunctionCall alloc) {
  isTargetApiCall(alloc) and
  exists(Assignment a |
    a.getRValue() = alloc and
    holder = a.getLValue()
  )
}

/* Predicate 4: an error-path return statement: a ReturnStmt whose value
 * is a non-zero integer constant or a variable that has been assigned a
 * negative error (heuristic: any ReturnStmt that returns an integer
 * expression other than the literal 0). */
predicate isErrorReturn(ReturnStmt rs) {
  exists(Expr e | e = rs.getExpr() |
    e.getType() instanceof IntegralType and
    not e.getValue() = "0"
  )
}

/* Predicate 5: in the same function, the alloc dominates a return that
 * is on an error path, and there is no post-op call on the holder
 * between alloc and that return. */
predicate missingCleanupOnErrorPath(FunctionCall alloc, ReturnStmt rs, Expr holder) {
  holdsAllocResult(holder, alloc) and
  isErrorReturn(rs) and
  alloc.getEnclosingFunction() = rs.getEnclosingFunction() and
  not exists(FunctionCall cleanup, Expr arg |
    isPostOpCall(cleanup, arg) and
    cleanup.getEnclosingFunction() = alloc.getEnclosingFunction() and
    (
      arg = holder or
      arg.(VariableAccess).getTarget() = holder.(VariableAccess).getTarget() or
      arg.toString() = holder.toString()
    )
  )
}

from FunctionCall alloc, ReturnStmt rs, Expr holder
where missingCleanupOnErrorPath(alloc, rs, holder)
select alloc,
  "platform_device allocated here may leak on error return at $@ (no platform_device_put on holder " +
    holder.toString() + ").", rs, rs.toString()
