/**
 * @name  rq3-c2-lu-4-rep5
 * @id    cpp/rq3/c2/lu-4-rep5
 * @kind  problem
 * @problem.severity warning
 * @description Compositional + POC-OFF generation for RQ3 cell C2.
 *              Detects missing platform_device_put on error paths after
 *              platform_device_alloc (lu-4 pattern: dwc3_pci_probe leak).
 */
import cpp

predicate allocates_resource(FunctionCall alloc_call, Variable v) {
  alloc_call.getTarget().hasName("platform_device_alloc") and
  exists(Assignment a |
    a.getRValue() = alloc_call and
    a.getLValue() = v.getAnAccess()
  )
}

predicate is_release_call(FunctionCall fc, Variable v) {
  fc.getTarget().hasName("platform_device_put") and
  fc.getArgument(0) = v.getAnAccess()
}

predicate has_error_return_after_alloc(FunctionCall alloc_call, ReturnStmt ret, Variable v) {
  allocates_resource(alloc_call, v) and
  alloc_call.getEnclosingFunction() = ret.getEnclosingFunction() and
  alloc_call.getLocation().getStartLine() < ret.getLocation().getStartLine() and
  exists(Expr e | e = ret.getExpr() |
    e instanceof VariableAccess or e instanceof Literal or e instanceof UnaryOperation
  )
}

predicate missing_release_on_path(FunctionCall alloc_call, ReturnStmt ret, Variable v) {
  has_error_return_after_alloc(alloc_call, ret, v) and
  not exists(FunctionCall rel |
    is_release_call(rel, v) and
    rel.getEnclosingFunction() = alloc_call.getEnclosingFunction() and
    rel.getLocation().getStartLine() >= alloc_call.getLocation().getStartLine() and
    rel.getLocation().getStartLine() <= ret.getLocation().getStartLine()
  )
}

from FunctionCall alloc_call, ReturnStmt ret, Variable v
where missing_release_on_path(alloc_call, ret, v)
select ret, "Missing platform_device_put on error path after platform_device_alloc for $@",
  v, v.getName()
